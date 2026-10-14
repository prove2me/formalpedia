-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0389
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:33:45.878982+00:00
-- url     : https://prove2.me/submissions/04c887a2-9f17-4afc-9639-46602a4c0863

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 69784175 ≤ n < 69964031 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 69785425 1250 69784175 69784213
    0x3050c0d1101050d0204030c03060b130905070b0a1e02070602070b040f030b04081c060504060b34120509090106031b03050601020f030301080a03080c1e0307091d060a080f 75
    0x1d035a44013001882c264480d00ea0884101c001da0003125000c0d03d41101c0b058030f091402d2080c04102c0001c0040c41204c08560760242c54072070034055907542d0100841c00a40840c401c0700c0b80d6441181a94807070904209043d0001d40383d1b0050f000d4500940f0a50400040c03050b0800c08840841d500c080022510740d040d41d8420280b40000b4200b501d0384001800440c0000420448404550040d00d0001854518100501041d141c681d849405800824084044000c0b21103d40c0012400602440d0102660200c507920813400c40c00005031019003560460000b09401c0710003003408040440e5990026a40c40c1802c40542c0e420307103202241a0170040718410131501030f400c040e411140500544070880203100410345590000d901c556555440410308030305141d0840c3d50980c01451101d426442d0241201c078944040454260401d10101e00000080456204d014103c000e4004041070b104000e188a01500b2403c005641280c424841198005140400080e0390101c4096170400340c45803044901c20202c0c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 69786675 1250 69785425 69785437
    0x17030904020d1b1701120308040b041406280e0d080a0b060d020913050c0427020415021006080c0609040b04050903030403180f0e07090807080703050c0d110105 70
    0x205884420720014110344001c418060043c0c1e559003260003428116035040040180c0c083e0418101a80f04080031a90001c0c81b05c2d44290409180300710f03a1164074240703104216119034115180180c0052209600108503c84030a503010401c200103200540c03038140032100c01034442e0038030798403c140d80f0b012513001d0003500382c0c802a0181c0000f10520281c010403040e5109140540d1440d500040518591602e8402c0038601d8038910401c01c90b9280c660b130541814402d0380941442c0207000403840c00102e2400901c0d1070340d1031094400355151135450620000c8800345255080c058007a940015000016034480d104c210f40c1c03080000c1140e07034452402d10580d503120301c01c6070790055180c206c5c1c0412911540203c6004030b000200a603a2481c0604006020755450b140302e41d904001c040c0100321503000140304a05544014034130380c1694071101000d43d0b40d200c0750f90105925001d4814005030005010403103400f26400740064030900e4060130300b0040b400400c2c1800030324038014140c0d0256194817403000b03000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 69787925 1250 69786675 69786697
    0x3070c051c03060303110303010303050403022202070b06010e0117010b0d0207050706170c030408030f071809150605070c06052b020d0e03070b0609060d061404020a1703090402 77
    0x840d1000d901d0558099208014000129846410070003c240d4022940d10340048188003070360855041d40d41c000d00ba0321481c44040e10585404041c1c124071000260030001211429104550301c421525004034801c2c0101d8003603010688403045400154007a5290034000328141040b2840782e82002d042c0344450700545040350a40358244402d20005001f00b0419001d48400e4640007541c041c0e0740d0783c032420039a005010404172807060003880002599281903d800ca807d0309941446507407040000c83e910f03000341d0703a040c40303101c0549000290742c7d400f9072040310800d14241000d6415130710752005403818403483e80020080303040807404011061040001d8214402500211340c003820301072560b9800284010507140f14660f0000c0c50300d40100c5248224500c000044002d903041c9041e640781c070b9108802c0200614000d2a200d40050050396506c942460200d5200c10200b01566901c10340f01c5034201300700e8040b40508126040803413040d20030104461907a0300c0c00029464000c60f0414040690400c1c0310f006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 69789175 1250 69787925 69787933
    0x90b120d091809050c090717010b04030c0501020d050906031518060f0103020f030a0b0102152e03030507020f011209030801051c0c1401121b020d0f0210020f040819060506040b0603070c05 82
    0x41081901e00315503000302b112502580e03c3d10304606055180c60b20720340c01135055500c01241c0413851900302c401d44801240c102c421079201e6881c500b495260420f01501e45a00040314140c1c0b441d20468101580e020760000c1d510b086003401a400150224400d1524043c1481070600006014100035084251000b8061041e62130b980d401075820481c0550588550403040010801c038005403c50101008282207190350f08904e6034035544002d040d074401c0c510f0103401109034005a04050740502c1910040000f1090304000c400f481d820001c3c640b080c01e01800e803084908151400c0c2801d920907508a04075003103441201040d00e4040140f80e0f016000e400b40e414000034840d91800c002503803281d400c0e60031802c0340040808582481c000d0900224403080c100740705056400c025055800611250008406040180d0f01d900009010303001c3d02455010703503411301c00c100944104070801c205800030640305007030602082e00c4110411059614240b1501d81010f410b000183c10b2911900007544002c2c000c1041c0e03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 69790425 1250 69789175 69789197
    0x90504081e04060806010c03050d051008070603090b01090b06040501050c010b060a170a09030e0d021f02010b0109090203040b04030e0d0203060408090307060810090b120d091809050c0907 82
    0x310649403464241c00c1907121022070104a611380000f001c0354816000d1911051103445960050400e005042035240080d50391000607101c40ca07200c0e82840501084404c0341c2e142580c462000f0b010301002e120440d0940626400091080828006e022084070f00401c3c1c9400c181c1400011034076904001d03402a004c2d0b403240c440314083e4940e000144090b498554404452443c024942d140401000c1c0500d0304040c42e103590100460307130000d4042000d02e401c442c0c80b01900c2e010b0000840001a04007200046400403521104450301503110b1021300d0320a8031000040760344d80c101c0004030300044030003420f9008441d00082c00288610208007525000511100d007112054012900d4504201c4080750307105c00000e4050a24078007081030000802040c50100c0b1f10703151038078501c1c09680f0300b407241c190f19a484104400e1259180740d450500c0d820746008644000700d8581c0024a94682c80c821445c8440006622556580d1107005042840c0c1d0000014041140d240e0140004401c0007000c81040001c80010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 69791675 1250 69790425 69790447
    0x506041e0b0c070e06030303070806040c050c07090c030e07030503040303031d030c0f0129150712050304020f060702011b080f04030602090f0102152e03050102070b0a05060a09050408 80
    0x1400000310302c240100102801d10410080b08280a46400d120340e005004014001341d001c0089903001d0b8003600d002c50002d07540d80080da114000c1521100f40d6004024012801d0549507004c5074014003240d40502c80010340090ba00e8a0703988030301000c1c00386e800400c41800070274000d030407d003000c2144101c008106584881032030b00395000440181070b0f86d000311703400c2c9018403403d01405014407054044070007154103104800039503000452040d805104250f40c2e189407050b8070019502c07102d405c07640b201c4294084010003405680b080340c080303214818003031000031203081c100c0941e00c40da541a10380900900c201c1c2401020a14201c070100c400000400c04800c1004a0f04040c0c0006e40c8201d10168031010705404000f410300c0801c84e80c03070440d440840005049842e10f09050780004400b490902c2c1c48590940d40011100e102078810054015144004101f11056005141075401100100c4a60300e0380e45070501a43c03000e50703609501415001e001d001c1080c4a40c806608180b00c2c0c60160314180701400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 69792925 1250 69791675 69791677
    0x608010509042010030506040b0a050303090120010c0206070210050712020d0e1f05010909020108040807030302210106110607020619180b010e0901020403021c0203251406040506041e0b 81
    0x1c4d0b42000070b0b84880031f101e103900f02400f90703108152080b15660041c0b070078080403d17a2401602c41c2d250400a05022114082303a10820f0100380c003100318000d0105041c0d6000180d5105010b86040d4018803d800101ca00603c4521038503000703d0160f42c032080700409810140d0b02940042c15a0300d0080e03913400d40d101080404100c1400303003841c0448040806503410718008212601607010b652610305101d02200142e80c4001060390155210300d442e52200340c80d04049009016071000021984850032a50301c0040700000018100d481075560000141d0352442d2407500d5500a5400001591010003c0b510300c844002c10401401600b903000034145810007081407942c1c45103007003540c0c003851080040c0005044004540d03407010740e002c02507282030718681c0402e0030f032542204020108044901004110b503401d10400801c11421010302186002031200791032401160b203c0c0c0d00060814000d14000c80c00c001064504480c00140703a1801c0500d029219410301d42825201a002b40c00c100001c00c480000030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 69794175 1250 69792925 69792949
    0xf05150a05010501031a060708071b0b090925050904090804170f1207080702060403020d0b1501090b1e0c060a0605030105070504030809130b06071b06080105090420 72
    0x20300100711540342c00009822140320154100004054101e031254549440b01100e0603258030074119035489405040c000c812503194110810041000080040d1015098020305021032080f2401c200d0740d100d0760604548090010030310b0309036007940c0d080e5101d118096000f0700180c0801401c0030807036010a9a450407198045e400030650500c880b030382c08440e65020025030808103106030042008047c0120181c8144c0607008004228002c0000d01404540790b180a0f5070017507601420f00c00c000040b5160003a540682154040c00f05119a20000c4196100300d602008440341010240d1908a40281078040d166910500e540c020350100220110b07050200086403080c52041c000042d01800c100c10103007503d401504c40001c00809020a002007034a030380c12581c002c40300b00d0b00751340c05100c0c13501c0c1c54000d0001c0410007075025101090b8075041c001401c140d000c000140c120500c6a282d11000181c03410304080c014950001e480d0000280054500f8000d4442903188440030002c8600400020361090110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 69795425 1250 69794175 69794191
    0x1140705070807060f05120c091305070824040509030909040308091506010e0f03121b060105030d020c0d050c0d030306171b0f0402090604030501020304031b0305070f0515 75
    0x5028200241c6500f030140328007422580c506400c940f1040b1800810031b0241403086488200600042003854248c1c904981715078001410382c0200d01001074843c0f0044c841101c0c0c0001203000d010010700c418a208020b01f00c0602030704800c41211101c2c805020003804020800351092004000e800042e80d54100720742e104034070075034603416a450034821080c1095684041242490021010302426030b0300a681010a00c0b4140d8031400c407075007104002481c004600c9007202c4007070f0001070b08540001c940a903503034107440c05c00112141a43d98405140e80c900c0307a030a42c0e40c016000b2440d204070515000344203c00041c010b000300c41d41884020000f1ba0700d469021011070200341e540a0420580e01114500c001151204010304020151199011608411440310703d124200300c1203628059a6941c2c1981c00383d001c0608607c1d21130341c891911074000e5105a6068007c5502441d441203016444241400c003194140c0d2421304000c419070300e1075040c40103418211014007500c0f0300c5c0314607003606040e403911400c1a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 69796675 1250 69795425 69795433
    0xe150d0b04092d0302070e04020d0b010b031503060402060906070f0507080d08010801050601390c030605010e010f0b0f0d02030907030c15050403120509060d0c0906051c0b01140705 79
    0x880c25010fa007405459440e0180c042d400c001a102298000c507100c0d044078004040017415030340f14400503095003030320000240242010704c00800c10b141494059071142c114050032180310b00d0030104050355120125402548031000b08007404440c20700801400c41188503245000203150250b88550805a16400c21a8594800c42030849056030240e507103401040d00070700030002400c0640000744a07070255528150001c1008a80c00e802100307a003186c50100e0000584c607a90802c0510b00071504000300e11058a660341800004540c941d082e07c1c220b4100c42c0120000401140303020002c0445401030748040b000400144800140100103000844c401c007040c1000e00381090035883d0606040030950005003484c0745580c81d003400d0300d1f048401c403803d03241c12800c00e210b4031900040c1102c0343d20903400896001030000c40e44480807044c58005100407005511200002c1c0d07100c640440d160300079000f0344801a000502000030004080e805140c610b1018506556007105003c91003001e0351101c40d04555540c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 69797925 1250 69796675 69796703
    0x2120d0510170c01030908090a0305030d0e010c20030403021816050a02030f0d11042402010504080f03060310021b0601120f021203041203050406020d0e150d0b0409 72
    0x1e0190740d4100605014004408584652558240c0d20740395055a0b6051590300c00346503040c00a0031069803103007007008100220041d20780c0750150f200c5d0080701500600500b80405004085010b0207084081580da41e22a0b52240404000300d100f140d90302103040c0d460008210110258440140c1050701515041242c059030510000341411384401c0c0c125441040000d0205070f103051b5012040300c00d42c1084000300b9444d8100710504100410b401102486a41400940050a040e003070924040c007403e804100103121024040590aa8004480040800d182040303000403084405010359007018015048480e2446001520012030f440b0307034000b1207111003d030300b600c0c9140700070080980035064202c3d403c0c140f40000d58915420300b1071020001c0c826107404034001e4a014003001500c0c0182000b00c030603800c180300c50a01400750b610a0003914010b01620f005005000d00801240d071045070301030206ca400708500942c22a0a800c6083c010b900191034400010043c3d855000d90b0403164016816040b03809 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 69799175 1250 69797925 69797941
    0x20f0a0e0406050307090e010e0604051f06050a0e041a01030c0f080c0a03081c020a0e040b0108060d12050d090803270a0602070f0209041212150b0a02120d05 69
    0x14009051040c031aa040c800103114507100810b070001141c0503840003041f0101010191800341001e40c2203150540f1815040000f4003000103400a811400c0e44103006000025180c510187d401d54040c1e10342007601c0803010402401e24520040d482070246181031030303044c022000c1306040740c0c00783d0080d1450b01d00054180203002d035800b00c0c6001060010001c0003407a401401045c0540000e110140c25020701058005081c4116140c2c00b402e04103090742150364440701c5001503d091180c903407681c0150310388100036105500502c0f1041c02030400a20000240b4515aa0014055400f40c58239080000c284140a2120301078000d490440380714a01068603490041468240d50896032040900c0b0740c44508142c1300c049010485841254010002680d11403290a0003440c04502090003500030f500e090800080c04060701e0191a500255a6031500c8810003424400541c1c294002c05120441040e5040000c0c0d00c21074018102c1039810f0040c0c0d954003440e850400d00c0c0d60041145407a049494900300a510707 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 69800425 1250 69799175 69799187
    0xc07080306191d090618070b070203010b03120d0b01050702030a02040f0e030a050d1503030504090e070e0f060f030c1003091403070c09050a15050409060605040f06080616021915020f0a 81
    0x3c1b190701ca540314a1607599500d100c540304952410000283c280d00390f4401703400c000c5400b01c1c090225010a06480e14000955200402141d03040c0e141c9075002d241c0790b1243c4100d400c0660001c0041980171520307002c100041801300441008142d4400d542e203107170315007070019041c150410788640e40c46100c11160700040d1035616003000e4a0404000301440041c1d00300b4243c80545e28480d40006880d0b410b000010714081d140d4000c0702c0781503801802c03c01800306142c4600e20482080e00c10b00e1406d0301181c00c1c140c0e00d80e0102d441a601c0802c203440a4400d5200b40d0240d40341d5030007036142c0560300250117041c5041d03620000d800c2c0d4800d030100c402440159003c2c0251a080800410100658800034481d44140c1c085030140d030384210380350071440c01808602c0d0010030180100410801c0142c901b004102d00078840c0c0e02c2400c0b4a4004c40000950709642e03003080b00c00c601c109030007034101010880c0c800c030080d204412003207c8030501d84400001211152001d0003c0100c2c0c138200700d980d0501104050300c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 69801675 1250 69800425 69800431
    0x206060301061d0a0209060f07110415150c0b0907060206090604030906110c041d0c240a14070c0302181501030e0a020303070803040b0c07080306191d0906 68
    0x181e810480100041c4031001c0141c04900d404441007603003525201a05800b0740b013815441903001134041400c03841003001070000e101c003a01c10b0380e42000d021400300c10b01096842c01c01102d01c1c80c80f00c0c204100030300f6164060b07604400e40c0c14603259440e03030a01d50394001c010005070b90300c481c941c0c0051420300103240c040103281e07001180b004c020505882d1a035401042a6202d008080c10401c15011030400810108080103c00ca0001e00602c414420003200b40303412803000e400c2c980a84600c01d03040b602c034207044074078428865201e800c8490b46103a4800c2c1060650105050504005018000a203010300000c0074107c10303442901d803480914079500400a403012061240104550700209006c080d240030a11028603200a0801190460051002c3c07170405036405800780d0580400a004010410442e00540c425441200c91000c1c5172682580c6040320301902000038000340b0200040741d001d10307090010003d045050b0900101880e155501001c08004040455008248280500003001800d10a2541c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 69802925 1250 69801675 69801679
    0x4050f03040e06010315030b0906090c04060308040b03060d08031e012103030507050903150105040507260408070c030305180306090d050706020c060c0712020c090a0f1506050901020606 81
    0x10625007090308610b000880500600d060542d56102c40e001d0107142c1e0240e60045401512841c1e0f035103800c3c3e11140e01c0307100c120b900040502070f4008000c054603061060302e007a66044007007d03041c0b078101580301c006584060b021690200488002c900055100401540304202c1d0310b040042195030300c1282d03040341d00181c02460a04c0c00c0c01d9040c8220000344404261a07031f40624003c039960b1252201a1542d00c0303105402d5406000350f010050001c4881c01040b41255020f542c10041541d5400c4100c80002810b1980a4405d42032202c0c00c1e4901d2110b503c00381c010340115100340c039020f89581c0d100c00d0400d965104402140000c516008204a5a01824507980d0141d010300307c20700d05001000d4942c030441e040c5030306100c00400d0101c03c1c401580d050700c580f42403c504803030260901c444101d5454112100c2101c130028000c4c82c0c0b000e04c92010030410208000038108103150340b250030907000908030348880c44040c507647d1100380b801e4520220120740200301544540350341c1e01c0c101000a0510000411b454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 69804175 1250 69802925 69802927
    0x50606070201170615030a15141f020c04060303030c0201050609010b030a020706021225050f030613090210050301060306080601030b0a020c2425080105150d060e04050f03 75
    0x10015076080001c030030824070084103e11990759000300043c030100c180c1c0342c3c00c14a18004010008101d04a6000350b07114130518400c1c0e98800e03a90300d60814490001035800d03411000a0f0b0fa0f909003404440c410b810a0b10f0580141d40403085032001180842e4043e501c00d030b000a8890201c0005c46030203101c0d05800c6003050b81e081d01c2c0f5604001c860951444007500c81c2c0107080c0c1c00038403c0c081c0f1180f41d042d141026801e40c14915a41483c2004550380000d175001140c204e160520305031540c0d801041280c1090300a07504090031a680c2340c0812014051151144803000d4031254072200680c0c8801d43d044d41c0c0b211030b8484a13225410404000c084410b2a00a00d80c9540200018000725100402803a8000504074000d030390b034080c0005003810f20742d2441e822011076010710048141c0510903886144210340700d03c42c01501c6940f6640d84145980c14050032404540d4400050005003480c000004a25821417510b9240c142884d03800400c40f000b80e8401c000b04074801c030900040120074040303450300b030304190021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 69805425 1250 69804175 69804187
    0x70203030f130f0b06030c04091104050c0a0c020d0f0210090603110403030909020f040f030605061807170a06151d010c051216080705030711120309090c040807080f01050606 76
    0x1034100c00c10f03010302800d001125000540c1544d81080580e5618202a0013480402200e19150303003048994221940b18904040c0042d8409440a0035141071654a603904170620542d5001d0028007a030400d8140c8413004e205140d0400341e1944a0001e11441c51039481c1528185048c1c030040444d5010350b520822800b00300400c00110343d020355000107980b01c040005a4440e15240b183e869031060b130b03001c010020040a000010f005541d0300451040f1019180d407901e14050150b15900c1c0c1004448800102c3c1e400c10704510090940084507070310200c022000503142d5210607045801400d200e4a56000640c1c4404407401d801001920f0700341c1c0102030911504440c0a035603860780390b0b0f1074802206161040440c000031030a00105021041a8000103055035031005070900c05d0300c0ea072050406071541007078201ca40b01d09051414146840401000255083c40c40201c200b0812003809020349810650512003c5420f0344140f018030010140c002c01410400d10100141d82034810040410740b04203c14448 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 69806675 1250 69805425 69805433
    0x7080c040306020c0a0c0b040e010605030412030c022815020708090907050405150403020103150e01140109030c060801060f022e0f050406050604140903070813080303070203030f13 79
    0x280c03030550750b20450250301e40c200154218a4010203d4025006000d5804005140c180440040c015030b4401c2c1c111513556a240c07070003a2901d10083e170340107010300c1244482c2c90703116110b5844110360882900c10b07035034101d08020039801840034030b41e420302d80c0c41d07003080c0c00c0da0230040884507090b0800c0c1e41c60000e6042c03500c5034440a109003e0551401e00072580440007410103032041d4100c1e0043c210081c00a031300c1400c0306400e40a141c01c50b02040340413900e0240032511064208076000104c9100024018580e820946984c5001101d0036009040c09080b82d8044001109445a00c02402e802c1c0c1e1900419031400000500e00000710040400303540024068a416040c141140c0e400b8081c034410015214116109000c006c000d150b07a0126910302c3e21050204000c41c0d50421805040c00710760070310031003266034414480c1d0607007618840c032039500412074000010703200d20181c882c459072030302e0001d109643c600c041411584101c8240b030046c0c1001040022151800309240c1e00075403504000c4280c010b80f695 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 69807925 1250 69806675 69806677
    0x2070e06090403030b011b0803060a0909020307090c05090d050d08070f090b0703090803030a0e100e1b06090307080319030b01051b0c030f030903010506010302072109092307080c 78
    0x2c40902055158401c500003a4003a4501d91003131010007421300c1e0400010300b07200c000c60f00165202c0303101d8400c1540014082070035001b18006950000c001c0d1504510300741155004201c01e03071540e001c0c04002d221650703681e40ca1940e8040d4107401032000d0402481d101c4001805114000c00043c00e008a15806e450311f6a40086031f2030941d12001616681e906007400c05850581301c69000c8042844000100020790143c0e80040d001c091586084905084213038201106942882c0012842d0744d1025840b00301c0c1a054600e22081880064245864803540c640800d040c8815500000d20b294800a804117000b01c4001c0e00b21140489458100074000d00040001e1040c807801000800155407594144e20340079080c400e80305c54800040842d009041c01290051700c07a04030703916451295190200040b8194002c1c021070301c20552040041e01552484445114a8021000c0420401540c0c4a000c14011200d1241680c84810310600c101c400710010f040041c40c510090440b41003104c2c0b01c041c0050015083c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 69809175 1250 69807925 69807931
    0x60309070e04050316030c0b0105031c0e0d0f080304030e1509013f0f0507050f07030c05070612050a140a020702030c060a051b010e1b010201090605040b0702070e0609 73
    0xc050400d0754582d400c2003842c6005510350701c00b0448404503440101a0005000b05a90b48503062180242e80d84404160705c80e62000c07120100c4483d10016000c0041c4264101c4503240301c01400c0421015941d01c03551244030340da0104036056500001448185504503e447d8815807044640060311140190511400d00625441c10706110040201905243c1400100340d05005109004414020690700c1d000c44001c0501c00d0712591894140386c0d548420b2580180340c13044419407203c503d00b20000a018483e54040340c02902003010360030340362000170428071000c0d00030300460745c4201c4490246450f01d03084400240c41082ca0358500282005011040d858941d44840106001a203075412400824100341002e408903a100400059103441e95800502501c820400d002da40440c03428086802422103411000c000d555600040030f000c824400d18009101488040c4000314603d001e546c0c45401756034041d40d0443d5505a42c4041041e44e41e4100b208000074600c4200f01000c500300103000c02c0c00c1034000703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 69810425 1250 69809175 69809189
    0x812101e05130c051209010b0f0301020405090112030c0b07050d18020307030201120209030111120105030703110411191d030d0801030f02031504050f01050117030d0c140a09031106030907 82
    0xd40d0046070300340e01910658840040c0c4010017000d034034021003485e00811680500e40d10800900d0303800401402d0503c20350301501c4028042034800d07401c140107a181d03440b50000c00c40c1040a0b048081c030010308800303c614003030ba6076030311581c1c0c507031360f0b07002030038055418100003030b5507844507480803030007507a0300050b13100c103d07034080c20103141e100c20315440782002e440385503189a090743c03c10708004d4a400ca100010600d050803030301ca072400c90740c0318020580c8a0420348000b820070901d00a035038503d40341030741c0710304007a40346400000e141030080d210000403e4400004080480ca246000b010f603142c40640b09140c42c40e0407070107805078a2464602410020042c0070141c1003c558001c440110f48041140b81c00403449404600c015180c18540b140e601c480001c07800010b5401c01000044400e070503080303103a4524202c00a542072503114605240101004d60006080140f00265954040307555802000e03003005507602c40f0001810350420080c54544644014001c400030000c0150189010654034241c03900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 69811675 1250 69810425 69810431
    0x112030f0e010210020412140a1205030a02090a080a0204050c04080d031d06010e1006170c070c03021513080a35120601021009120c0812101e0513 64
    0x41000403844c140341885829420b510005000c07036040c4400041d2440f0601c201c0c000380c43c111300c040066032240103d03140206403004646d5100340d4a800703600550f0b0b001c00300110040c1004042d50001c1d0b03100000758410240c9420021003c0c007507080c680a000c2d031101c03282c03c09905c0c0a180480309503840300840312000401d42e0f11040b540d038041d901c01030440e516900307101312000707075071200103011400308181c4490a14200e0400000f42c5240620b170309843c43e140504040211f5520540100000e6100c040d00b2070340312901c0c10010005079180f034551902180310105180d120016542c00d00084242c40c1c1290380e640c0e1000d074003003002580c658150348003d15030700c008960012800840d10010202003240b10785880c0e02041e42001d140101c5829880b51609038201c4180c0105407400004858480101820041c010380102640b00d024200c0c0c0125640706c1c040c21072905403035102140301c051050b0340510310281034100c1000030001e4401200e17409504440031030340d46843d1600050890000282080300c06407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 69812925 1250 69811675 69811697
    0x403030b010c1101110703230f010c0504090914010509062d04141203090c180709091107140d03111201030b060f040f090303180f08032206140112030f 66
    0x4086c8007082c000d44c0c0c40050b07070507000c1c600040441c030401030048100c1d442c800c0c41e00c0d440e12034505026407880354030359443d2140b90904000c0c004000c0c10300e2080684215100d581081c6010100b441061b1107000c010003e451541032041070003003a401071188003d007013030701c0080080c00d904c1210303000c9800c0b55000c0081c40b19144640410b904000060030b1689004001204101d00c030440811340034043c81040b031ba101042550400488115036040da4000002500b0f44400e00a1880701c1e4014085400305410407424124140e803540c2c2c060040c42001907840c0c0002035400e841d02c3d0135010340360035012903603010b074202600010207010031041448050042d5601102007001c80d140c000480301110b2000c0c1003801039400b64419080a0919401c0840000e4070b0009541d08030320304100800d540aa01480c052845400d0352607a810680002d0103034224500301442c45040604041040e00c1a544900c80200700603120000490600070f0507071104440501e4031082d140020b511080c0301c04a5910340c201000740c58 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 69814175 1250 69812925 69812957
    0x19030c0b07020708061b071112030d0f05060904121206051c03141305010804020a09020c06041103010216061802061308010b03010b01020a080304081903050403030b010c1101 76
    0x440858000d00000006014081040d80c04107044054914400803100706032103e00034200c4481126031101c00040c01444201c002031170321015031081c5c0800030844c2401c04090094503065602c958004001c075a0798180f0300b0401042401415407100084610040f03a240c907450b510554042907440c24208079441c07080007000e03030b102d80c002806020003402c07030010b8003000384121096601070b5205070040b41d440403c02c5159030015040301c1a0041000c207200300d0f5440c000055402003800b5104991011ba0040045008200b51000c0e0446ca12140010000c0b82098180301503101c01c4040401c0c0281d004008002e031980100b030380801195032250001800c1c0484084070805850b9942c4000e41c00f26000500f5a00016146d01c20b100340d80400008108542190041600b01c80c40c808006025802a8a02074007161032207000e558414080c030281c83c80c9c030b00414081e41c01d40e0350a0044d100800c1e0364900380024158184507400c010802800c1083c02d0000e5522610016030340880c00070304014104180300c0b806 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 69815425 1250 69814175 69814187
    0x3031404030f0b180c01051909170705011211090f03010207020405040602030a0b0a050d030503090a0c030b0f0a05090703150b0a03210c0b150d02030303090721051903 73
    0x1542c0241c04840c00500714603000d010b000341a079903244001aa050580c81040e00801c08100700c100584500f440c00c8c0484a104200b41d00303a0303082400b8440c14110026040e0b84103552200181400c0024042c2203080400240660170302c0c0c0030841c030452400d89000c18150002044880070001207941c040d201c084d0b080001d01a1045000080d040f03400c01052000b007201c81c2e0043c1d806818034034410b0000b01002c2051120f01c2040344940c0798440c08242c0781d240801c0c00354000b90f400040c00c400783d88618406460b4401c41c624103074812104040f040f410405604844401a504510702d500305100c075003440803100b1b65440e05404041c0890840c916039034442e050f65403000f98000e0f07025051005855490400b00c614001c404500040145145a1110045d20645c9208011a409500544541c540030840c1c81400c840c840c80310341001c003550409015071303002c1002e50b11416500e40144401d034107000e281800b05031001ca90005a5000882e4000000d6011501061510301c000200109015600f01150030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 69816675 1250 69815425 69815429
    0xf07062a021801090b06090915010201090503030103120306050108060303180102011d0c030f03070f060e12040e09100c090e04080d1b020105060d0b13140d020109020103111303031404 80
    0x710009000b5003a020440d100c000d68121503050340200200e07001c020078004c0300d11460590710342c8203c001001074481c90070080d500484c50300601c000a411344140e40c40d40c0c0703558400e8100381d94030000c0740044a103165050241001815080ca016105800c00c2c01c0404c0d03685c06406421941c80d81500711008071a4401d40c85400c0005585640d401d42000c8144a5500d8801858407213000740039003218411034800c000200d540e4154001e034202344101d81519400004e000040020180740146a4500320160407170300508082c00342030300e610030305d0309014040b1407500c4280c100072441c1e1340c00c21045a5046070000d414404a5940c04581080c5686500c0d022589105e01152000c0c15464081c0c200e181c8a400f603000700241031746400030030040e210041007250803402800003d02030441d10000580c0c0105a207006440e241c412240f00b0001a0000f054a05015050750b940f00140e640e210000103542e418014020078086003075119251011881c02c140ca80c0c0341d1400003a0a000e009849428040301c40012900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 69817925 1250 69816675 69816679
    0x515030604021b011d010b030604030509090405070b0f040501020c0a0b1e0904020f04031208040f02120307020307150f080118150b03040605011403160612090209041101020f07062a02 80
    0x89421079000b1070040708803841c55854291f03e464182506802c00046080c090703501a04e4103810311920070104440128000d00886550083d031f44005800300c004805804c165103c0d08845840d41d0404000a10301004d10605511a4103505003c004101240301100d03c0384101d80c0401c04542d045601b03166481c41038503d00b581191001800c003082d0b8030141d000c2c0041d03911600c000c0741c031803601c09000c07604200c00b80c034080c200c1101d05103010010725090046010741c800708401d9a090944980000e4104002a440504a0070b55202c5580402e5400350340403041e0030701401c0120155050403001e0000040c140f0038130781250340c0d61a80c0c000806605468600514425160720303943c1c03901d4a0900044d04080c030400c007400c1d80c02c8640c14507524010440c0301c07200e469845025070740c6250110403500c200f015044000180d90700c8401c400542c0718080d00521843c040c80c070210211100d20002883c00301401036158858000400500489030700440b01181d2615081c440201812440e00001144040c884025 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 69819175 1250 69817925 69817931
    0x1202032a0309010b010c0c05010318021e1219141e0706180315050604060b04060519030204080712061506030f1406010203090d17030702060906010515030604021b01 72
    0x140030100000314031070701c124002071007848080d5005461748142088024401803a0315001d1225500c2a403100c016240e0581240014030241d4010408072040d9040c000c000c40350034069039055091a0070109a0011131a0060800d13100100600328103948401e4014171000140e1080c0c8001e0001b00087c0b020342903068008000803186003800703503a441d100d02c542e0300410300340c1308004110341080c11181d08580d00301e8403141c103020060f400b000003030400815265010fa503d00300401c44401a030b020300054410f9489a66540e0000d402d1050a1103c54007184202342c0100000e10542501080301030441c3c8003940310600282d05443c01c04054416624808401e488001e000a070041e410380180b101c8002c00c080c00c001d10300505500e6900b90070116201d5003d60b004100704000e030b00b8811440d00d9a0781c02085015400c10781c01d69080b10341d40c001d591400c010307449282448103c81c818051a070051004803030038200c00c9d0407080b440040b40001458648902e602142c00c1d05a140740050141c40100da40000f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 69820425 1250 69819175 69819241
    0x1060b031303020d170c03090115090e0c0906030a0210020109050105040c1d0907060f0219032d1407060b03010504030801091a0d06020912070306060315020307120203 73
    0x400982a8900c010b4005110b200709100d00113000d142d040d01a24007403070b0072000c903980b24005441c00d039002a01c90840c82d036841c0c40564618030700010b5900039203000d01c2d012480c003204206072880d1103e80656a072080e2403c03420b204940e903000138412200c1d641034604a964041d00c100036401401030790409003240d400c20b020041005403181550701958060080c0c50004081001c00007840700c000c07a85a08039030300c1600c0500070385016110014401d0720700d10450b114800c01c103a5885e0080e24500b000c40206000301424811442208542003079401c4100301c1d680c6066a075603008010059801600400000c0007404205103d280e802c001c2c003820024000780403504241c0340082c00c0c01d01c240b040c50445840c0c8210901480380c0ba640341301242100604161101c59640c0f03d100c0250b0040c541241c1c000702204801b040300340d0600c000030044d400342c400042d40e5461428802c821040310511380209a10400c10415400e40204550751044520940140c8950f03503403982150074080880a00654421180c1c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 69821675 1250 69820425 69820441
    0x2011407060902120d020a1704031709030705190504020d1118030c03070806160203070b090102180604050105220503010608010504110913141207030c1205040506070b04020301060b03 80
    0x10440d882c0748207854542c00d90f0400c4594a803600b0104c0c0a50005030006620003021520504030220400e00c0b40740520729140d0349554100c064054030740405c002c1c18011542e250b96107400d00c142401030509452084010030384c00d40c0d1400c003800e2801040e118607400f04840902e0705165000240040381207500742c5d80c030344a929450240b2140d00119a1080c4141d40c00011142000b042060032111000c004015548541c1040c400c0380c815140e441c01148024400c20010402c110380850186a6410006070f1f1803240c1c1d000e0f150010303038401d01c9a0242a08010410150b60311004803903091031642a0381d29401d81040c011201040e05900595066081c4680461120010361020b4040d901c10142c0c0c03c00c800c503000a12000c61011510401c00030b9044c0034600c04240d404044220300e00e0190300342d6a200c51403026600740754000d1a0241c0000d40108048001c01c102989240078190b441d0520030b081c0b525040005000384141d541c02070180c2d1195020130304541302504004080c21001040c2516841c000b20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 69822925 1250 69821675 69821681
    0x70507060c0e03250302010509030f060f0711030301030c060c0c0e070e0a05030705030606090901090b07080610030b060316020102040b0714060106080411060304020f090a0c181202010c0201140706 86
    0x41288640103010000c20b20941513400ca0b01407a80c0320300c4803054945180c0043d030710781d0083d1507200d4260144000702a000e040030700c001da201d070300d0910602d000343c02d000b04010b14420800941521550041005101150103692284101c5400303241c40790394564186130030401c112240d40845240c0324a041440101c54210791031200008041d40d03100780883d074803410544c0d980300030700c0ac05400d81c0145011a64034102080ba403603100c2404400410010f20954446004407000c440003c0000e41c1103062246518061804015080080c034003480051080d00004546100c0900809420008440b44a190900030340541d0002e0060841f6103865917010b0501550074407034120181003500882c000460001e0145410902a41c2c100c003200050030f00300340a01c21160300c0030f007080e80e000f4064441d660316a07a0ba00855441401d0b5140003041c0001804005400700b08003410150807498040d4050000170800c0700155140c0d030302481c110168a0003400181c6801070300c0409c1c5c0110480c0050410144031241d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 69824175 1250 69822925 69822947
    0x30a080c01150e0115050f0f040302040b060a090605130b0409050a060512060402060f0c0a030c0b060102010e0a0b04110a090b03150105010e090a0e0a0c09060b040308040608070507060c 81
    0x24000303001041c9251002001003a01d4028101e66680c3d0500601c502c01843c100b5400720111810801e142101100740418a80c000e0524205105400181802107043c14099450070f040140c40940c105400f692025001c0034181c05400f003013280c085886035460200000c000d00401d05800040d03603441d01d52442101600e42122407225960a200000410303040040800300d600020401500080e04c130355003000000d82c072203504290684014044800d051505100d0310002e14800d40316540200420320f002e00301d942c40201a581964034050301d80790000f0001c10409061a0b001450800715502c40c1341005019510b00705154004e51600360102d072041c5a5030103051490350881c1198442c885003204984010801d01499000484090310386444c0d01300443d2041d0002d40d1544003140005c50003900354589903140301d0580d04040004000c10182205104e0341d005480f5401c4003600d00b90842d160700d4a54800c91190f402040300c5c0c1000114000c0c41101941d00701e5a1100b4180112115450700418a800c08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 69825425 1250 69824175 69824197
    0x303031b0203030403051207020a021003090b090105190b0a09050907080708030f09060a0215190e030306010206131a0f01030605100302030c10180b070b0f150f0f030a08 74
    0x40030311100c106000100b80c1c0e02c5181d065451078580a1030b038081c0245442d015014030294071a540c160310042e65040111074100060366800980046141451500228040c04082d078a0f450038090004e80b035880c4c090018590319403000071807140c1d020008100c5070700307140d03008100051404060121a01010508108951103801140c5a10341c03a48405922840f603420888040441040190010304000c8094003140c200d60058482c80003402207043e0f044030003118120307810b011500d0905401c5989114050300d183d2171000031425440e00c000042c2d0756030405019140c41e0300800c800c007820406101c40c0c0d0300003551141254001402c050080701440042804111241350034440041c0c0707020700f0107131000e01700c0e0b030024014030200020801b40444118482c800508210403401030b41e020702200d02d403c1c3c0c02894980304007035948070b042c24881c090b000301401361448140341070140200c00090b44102405860708440b50002030b140003000a032981100c003069078141c058110214180060140940b50007100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 69826675 1250 69825425 69825461
    0x30d0603020114030f0103020108090a05160614040803030105150c010608010b040e0a0209061215090a1106130509070c051608071202030616090f0308030a0c03020f07030e0402090406030303 83
    0x4403400518940011540c0245d0101c90320300420156100d0303605182c01060100c103842d42403106449003810602d007520501c1414400020820000764807403004044182e45411640c00c05040210702a00c03840184600c0f8841c50562030000c00c2c041d0360000f216000780742c11000b0090350740c0d20384141d4080c0003110a494480c501e0445052103c07000483c54030042580140b520038540d0f201c10410a6406004210841074410310f80c9034100d5030314903007006010704120310080c030f8100820b2500e88620420100b41d40c2c0116810300122184610102c1100143c410449890345259140d41d41200c07014828070002c2c250f03218003200911000d184400290984031780000b510039064690188400c91050f41000039017541c0023200281ca041d550b61882e214151282c50211034032030340e41192115426441d081078a407441d0000034040220a41c1c4036648850015040960812442c000f4140050189180240a00c403003201c5003d0580e86030ba04942c0300c080002c1c000c00400b0380740d00b001801000b15840c06403654074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 69827925 1250 69826675 69826697
    0xe061909050a05030a030f020f010c020c090109060b0f0a180308130b0306130203061504060f0f030506061605070e180c030a0507060c050709060303050307020d09030b0112080c030d06030201 83
    0xc1c02c052800c25144003a00614401d83d403560100c2e20744100e081480118040c1814480c2100307001c2c0a0132226514a50080006040b030100b00000540107a00103004a440c1800030003603514100d040d10b04d100b017402001a06ca20b0a04001d41d103240203500e904004519041d004420001400040c100b40c100c0e44406004603929640003400d140300998051317611a141c001c041421501d60b400560b48440e003c0c040c0e40b04034078034000341242504a5000381003c1101c00c0900300c403299002c3e000d0042d03450145000d010301d00f003102c041002c0d4032512520911400e0f05180500602030b0411000c4000c107001041c1c00c10340c1c900024414a40a155817802100b4050a81c1c4e15407240303030000307008640716000406800d035146820320a840403c2207007801c4885010701c09001502103218801c520045000b501d4080c0c0d00d203802c01c802410308000381c0c440c1042c00124a42030000c034026100c1f460540300c03101d580a103210700300d08010707140f4018061f880840c0d11002800305500d090b50b41041045034400c1c1c0300c644c4902c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 69829175 1250 69827925 69827929
    0x1031104050c1b010e030304060c0f091203050d0b030f010c0f0905090c0306011103160201030605010f0f050a09120c1409090604060c03090602070605060111030403031d010e06190905 80
    0x52800c0c1c4615000750b106200700351520024400c40a000141c00b400040d03000d140701d507810704540084506076036069592013101003085d00205501c140c0d07906032402c607104d030341820580741c000c004c8038002504220780030603d0b122883c07040d40320015030f0301d0003011521810000b0a00b1406410000510000200301c2c181d041e100318007940c108415107000a140200a5136104c0382c0f0314040c5c00c0105080d04015480705901d212560500060018032110700d02c0301c58402c0240000350550740158401c0d410806102c4428440a62010b030301e4a249595103070090b511b80c0c140034200d9541c1d04640043e2441000050440e003003128561310070f42203031510181140c80030110320411204103002c03140c0b00816041900000d0006030706034001300740c44c080b42c100003641030740703644078103040781c0104d03d085884541da0020f201c0c42d580c11402025000303103a034006510b0541141d034010200707031440c04d0300301045581c0c01c00303844e69a005002045044001802c81600c0b14001503c2c40b9041c02c408007882c0201d407801502140c3d43c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 69830425 1250 69829175 69829181
    0xd0b0d1218050a091a0603191b0e0405040c080f01050108010c0c0510050705120108010e060f090d030b0609120d0f0203070c0e0709030512091c1109070306090c030501031104 76
    0x110001007110f244540b0b00b1210340058800c084005030240803039822040d0564550303001c3d50080350043d40d0b00c90304144007410300c0304032051a070000c201a10072451191002c0c0c2d20080b040e50340c40f42030b100803138551501d2910300c41d0703008290803040c154003405c2c62101000d14150300083c101d8074404002d00000c41241d400b995804030074035000d82181c10980429156203856045076030444014980189024000140160361050070381140d50240d4682e521024002000c001450f00318521246002c09070614181d03c96840038039090503424980c03a4800c131301180d41c640c8141c03540328030003a20050140d41e9001c409a11803d040f5041c00100d003030b280813400c0d00c2d8400401d4038000780d07010810280d054104481c0302c6c0790b158000d0282007007101040001c40050743c00d1242180344401d1900341d98a40d0341000030801d04589800030001c000d607205108001080d83d00761041803502c41034540134490f84404e1011806444a40c1181104d00d080c05a0000e00d40d47c51741c00306040fa4094a81358120401e94000c000c15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 69831675 1250 69830425 69830429
    0x30302030702150405090c040306050a11090409020a05030607030c0f0219060b0402090307090606020c04110a08060d05070305060402151c020a03060806100e06060c070b0d0b0d1218 79
    0x5a0050102500504181c0034a0580b03042400c0f9440c1005c0d0b4074070000391309800842c0d4001014101040030410040d0398040c607500030044a00902940300c0f4040924441d0041c20501482181c6801c206002d6440b2103410380c02418016095070301d245400384001e0040c044003190040051030310300d00b01d994184040742019685890b9803000581d880310380c80380c03800340401040761580140e0030010f1503078503035040020000422100001003462840c00b50003a0030003004890440c010303403d0880c0d040c90070b003590045861f0a1180e0500d51550345403175010410f8059401b0009040d80700e50b030004800d00c0130004006101ea442100d1125001c80804800e07981d90180b0044001d1554940703409070248480c640282c440c4c0226450000340329a55584100d180c502d0075210b5212450400c1d0b014040d00d03801d90320055000340e003a40c11601d0321052030031035940d80b42a480340f0318080030f0120750204042c42c03981283c84107500c010006485641d141c02c080b8010a1140700d09804a075100c12000c010740e00c1d01001a003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 69832925 1250 69831675 69831677
    0x150403050702011d030307150605042313020d0b0108010f0b03031b0f010204031a0901090c180f060321020705010e0114070503030f0103050706080c0703030b0312040902070b01050a0303 81
    0x1c1444065401560043c901d042c080541c11007100750040c407610100050400d460084000301c55000c1800f10150403a0b8840d00300601480c117140b40220168280c003030400418010210720f040c196950684000840d4035101c00951040343c050010084c0940262030728141c1c1c004c0402000401c1c4c148910004441c0a00f001d02d0301604148840c42c00d01800300b1000342c010350080c040d078202c0514055032500f241e00a403c21120006201c0170903005515a41244ea80115400b00800584c140c58940d03444100451007052a0b100c0c0c070380d15040b40c01146030007159903001664801d1005a4991820240c5540d14480e1703950100e000300461240d9501c0003548c1001c5450607140c0d8521488c2000c01140c20055008000180750070402c013060000700108000c510441d100b41b03107890503504601d0301c1400d004465021004000d446814800044111811a04155414100081c504401502180c00c10005a8941003c2c41012078005105803143e00101460b034821030f8110f00b6680c0b98810040110f40e00c2c00f000d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 69834175 1250 69832925 69832927
    0x2d0309030b1614070320030a02060907270e070b030405010b09011503020a05071a100e09070b0702011e03020d0f02030c040e0603030d0603050a061a0d23010f090515040305 75
    0x50801c0d07800c03005000c481e0282c60002c1c030349403070b80300e101c6000e60401c20203003e154400a000c07208e142d4140901600100c000c00076200c803518210081d0318041d003061801d40fa00a100c25a9111540d8030350003090081181d005a864050b964040000d80d5001120159425400d10225110b5440c120308842c0c10781e51524a1a0100e4030f40d000110000e41095060405100c4208100000b18440c90341503021700f2031313614059140e803401295000c41d54195501c04201c0340041002c0c0403407071074041854001d8070307800440907458080710b00041b107009000100341c109120141002c184c020368182c00422407080403000a03c000701403500c4500032844221419020001c0c1448140221444103c1e425003001c002800c89090034108103c02c0c088407641c4c0e108403410f0b880203208600300942400b403d50032848124050202e440c062011864280c0000d0700103000100c00c030048560300c004c4204555000039801c000300300100351103885c0002000c00000642d000c0c42804040303001c00c44003001c13007803203241d040e0745407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 69835425 1250 69834175 69834197
    0x30207030c260d1d03030c0406030c0c0204020c0d0e01020d170622022512080916060903110a0605070308060307050909010b01030606030506030a2d0309030b16 70
    0xd204400c0a1041103081c000311081e5140d1042c06002071050441002618450010001030560420011000701c1d070001d00400042e4880141558122469400c002c50b4110084108541031a4a1030009620078404115401d040030006800c0310304002c5034491098904040d001a0380e500308401400000801084041d01c400c880341c038900b0303004a005042441e00e03800300002c00740e01282c040e0300141110b90104454645d800c3c020907900c1e040c4102a1400040405612010340c41d20305220040b0a0019003000302e55070090821540580b0080ca03c941c1d421a92107101c0200003501c039100950307441c0d0004040b10310f2450300c010004111100c3d9141caa00c4d16007192303000da4000f1402412113600d030007014000103091702c1e0341000c01c3c03142c0306c1c500001032128480c0e40003404607504c503001807080514102c1007000c00e8a001501e0f00f490354110700301419142c8802d4040c400c200c8e4941c1c1500f01c1c5524002d111041540051295003541d2044c03100f151199102d0300d260305211200210100054081854 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 69836675 1250 69835425 69835433
    0xa0315060801020a020307030e0d020906010c030c140c0a05060a02060f090a060204030804180603050606061b010612020307060e06041202010c0506010605040f080a080306010f020f0f100b01030207030c 88
    0x10080001001000410015501d580d40e50032030300010341e03a40160304000f5085040540c000ca42d07110002040351004426006a0089003c00c04020201c074140800d000764035040c10f0140d01c00c551800ea110961b203016030284400d407521854a02d40f210f01074940c400d0007048503d811400e8034550790543d07009080320381c2c440915070b0b00301d40d01806202c400d00400c2a81c00224410303000620145024001d241c0e03980b40341c80845250640600d01c03011201c7d02d00701c014000518045600d0340c0001d0100d13091a20b5031000b41301d900351000002c2c0441a0f561829100103110000138983c01c00e0680210b0940366000d41d10202079034001040d842c840d5001408100030f00602d842c0c01c0100029030b00603d030050500c0d10b59600d075403500b0001c0e04071a001c1040401e04214023a41c60f141d8001401044029007110007040d590706401d8000648814103006419240040703452007002007205035500b9034200c441031091105003a8807120169109144a41441d215000550182c003c6071802d41c6e0550f601c0302002882c1e11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 69837925 1250 69836675 69836693
    0x303060904031205010b1801021b0609040605040207120e0907020d12111803010b04021321080423040c05030a09030203040801151706040201200c06030f06040b06090a03 74
    0x8002c0341808a822a015142065441203034003800c007001815a8aa5108003507036074011103120300c070341190302031003121181e00719072207880801c0700041c0c0d44651100007000010300544950b4214a0700244042080d1041c0030b400d0000e841000a40d449103070320b08041200344038091004451050240e400920709250283c4a10051050414410b800066441001158a240f58804180c11014407623414454450380b800713204102d100c0108a404501d082d040d68115901c15600703110300e03141d003c5c1c220307008d02d040249500003205051313201c0d23070b107640d51038489406900000507415044035580e501150340c41981003078030030075803070003082e0b10741d01d0865a501c2741000250006450403401c601081c00000f0b0350213400d0043c1000c82130546c004204035400c1056070140000840e1124032035911403001c2c000580d800c4480c2a101010203144800c0d071003c54038005203000b0756094110781001c4e0000820484080700398541d801454100c0b0244180d041150401c0410702a43c0303500741c1c1c0000784440803c00541110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 69839175 1250 69837925 69837931
    0x5100e0406092108010501031b0c02031504050a060b0a0317070f0212030715060e1311130605040e01050402130902030a020a090207120503010f180216110a06030203040503030609 78
    0x20340803400710416603d0001c40304641c1080700708400e403811402c0c8800c0d00203076203a01401c02840d081140d000c0030b598040b0003101038000d44041c018100254810341d10180f15112041c1d105540e4148036040c03600c1d1642d07031054480c000759115031401d046201d19103424510902103d412401071124480310064485e940e074003116040b102c0e445240900c40060712244212840c0000c0103020b07503250b24039030611582660382d00402c014460314040d424800c03d908014000d420001d9292036060054040c030382a601028401900340c0d103c00710380000c03510045140c210300d003640d20980e018001c04400000e0303642a00c400781d8009600000701c00350180e4038800c2e0784c460100070b80000d0490780c4103040c0d500803440340317030b280d400413480310380c00003001c60a01c41c6402c042e8a0244652801d9440c542c03504810001c2145076001c0c9424005008040600030303152901a1103d002030801d946460125919240182110300d03102180a441a0030000078828003e100b0340e84255048805146076a445608000c903c01d001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 69840425 1250 69839175 69839183
    0x51602040203190e0615040207020a0311010c051203060f01020a1208091002030109050901050f04080a080c090907030606080c04050a03080a020106080303090610150210200f0d0f05100e04 82
    0x118900f01d00c10b40460190701c02c07070b68072440540181d0a1803100d101101640c03000207400382d4010401440181c80d10100202200d4001441e00c3c42c0c00358000040345d00300381201000d040f52045141e1f03914031120f00d90041d40a40b5044030200d4108008000581c1c07184080e03c400782c1200d44820700034540d14014964198024680b07016039214060243c0600d049030001c0c0c0201e03118950b180200208120240308207600407440800700140707450f00790396180c1c4034860011800c08002074140419560b00d003040c01e4a040110007010500e407403618540090007040700388200302c0043c030a040400c80d4070b0f000130101c90542d20b015002541090450b2900714203a440300d91800704640d0f8650002038100d00074409180a00c087c10040c142600b4420420038202e004bc1d00070000d21200380f0120346045400080f02c1070b0442c040980070a80399007485c1501000c0c2003150100c422000d0000e0311500c3c80b8440340081c20b141d80182801c0048a8046484804a40c01110030790b0000110040c24020780b601d07001896807003413007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 69841675 1250 69840425 69840451
    0x102010204050d0b0159040b09011a1311040e01180e060105090a0f090503030c3117010f021c1b08070f1b03050c0d051602040203 57
    0xd500301241c86404049402d694601000d001801070050000040c064896035030541000310541c0c01c4007002e041c5d4070301c6c078200707080e000d1244040401221030541802c00c2c005280800151815052105aa881c201c404505039440e104640b100318101074000c4c0001400505250f240ca082c6001080c02403070081c80907540c0f01014007001620030300440d400e134040c240c00510450060700420b1008180c1e903030b440100c00c0c0c40d040a00140b1146c5c80b00302c4c0d01c6030b02c4141c010002c503949050416001c0140604903019040b80000408c00500e0583e500013400031110b00400c5d40d10f04004038002c0504000c82140c241e642c100031795030811818035440f4402040d1454200009000d01c90038811604a91042c000d042030384041c200c2959a005503231103202c031030512910f030b404c0054650200007404001c00a100b48203210880c074541d0f107070300d1041241c0100500818540c4031000c0c55414050311680114403060154070400c0000c50707025100703000340c44800c08d035030303c40f440341d0f01499003000003940006003001c101c00b030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 69842925 1250 69841675 69841679
    0x30c0c0c1202011716090803030105100507060912020f0d020c060307030e120310030606060503250201020c01050f041e030203370c0204060902040305030313020607150c2312060102010204 82
    0x5004130514045d6880000c0c80807020a07091028084c0461070703200341c40c0c035042440104040c1c1c0f80c0134844880840103181281c2d4822039031814000030980e642d00940640307881e100c0001040e40014076a131740020340350225050045086800c030380d520010380c480c07500600280041504c45009820091745600007105072800304121a441d100345400c11a05000d00d0080000c04206216082c03040b130000c0c29030342c9000c501e035103004410307100d5000044001031520a902e03c0c00c3d101d601e100394140d642780030849000784400c0c182601c070403c580390140c40c1542d0032600011070b07600c21a4105903814540d1390680113542812207846120b01d0420428071600c184030f45500500180c2c0b56043c41480705601c0503100e18401d14103a0040c4411680940c101da81890700c108424408981c000040d203600a5181040c074200d02a94030100c0d51030b02a02000030189001c504107801d503d4002d410039841c03105035a5881c2540040020f003801072001944245110007c10031064074038001d200c5817240c0c08141030002600d019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 69844175 1250 69842925 69842957
    0x702030a0f030905010807050309060411130609020304050f010902011707091802031008060601020c1302042112030506010509190506040f0e0901060608060603040f02060304080a030c0c0c120201 85
    0x180e0104412000900104811300c0b6542e001000c064020b901c0e03140103400e51030641401c0e9a6082e01400c007405d8041e154205000a6454081e05950a85000c1d0f003802016584ca44000c041e40083c6c0d001c071744038020701b041050401ba0510948408580581d6108071150115010b5820004c010b0a54010015581000314442054203e8084102a410030040c1c1e02e141c0662810003000454200c4000307078004e88140b0109030781c0090310004c0d1400448142a11044015600000b8442c0d80d00100d4003600c00703000f08000314a0505c49016580c0519004d0b400482012021400c0741ca0403550307640421030a2160750118141508803905074281a000c04440988a80c001203440d041a40807001c0396170310b510184012030200d80280d82110004009000841c200704000d0922540200410301600e40030001405010441d070101c50241e0300582207607a41d060a050003a043d40c004240b40c404a41000c00c0c0080789881211800403594001c002d4459481c200380e40a101d007200a0402d034100904032803005400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 69845425 1250 69844175 69844193
    0x3060c0703121104060507050d1107060f030212070f110604021c02010309050a062304020303040e19020a020109032c010305060117130203070e07050405060d0608030c0a0606150210020702030a 84
    0xd80030721b8950725141c00072403404601d0100407800310403c0000d1706032400540c0b480064401c040e41e00a0600040580c85140100d0081c003404500d180441001c000703020440ba004204105082080e55404010300703441450142d50701002c0e50005c1d0080c1400303205240c0c80c0c0c15010140040e074030524020981001c151a101d01d0542d07801c10998546960340445c00c03808154000b100100d0b1401d0303041c480246000d800003602c0340103a01c266181d082c0c0420014400c00c24030034007010346d42c409140031500d03086101002402000f282400301d0104118140c0c0f040a5004442c0604034002544148a640d5141400440c082c001c05460241445200d160b00103c4141842c502440344080b01114000007030540101031400710a030b0320002090341041c4c244070104d0b030f100048a003946c02c25150141c0c0c8000b9080103a00600b80b03588600c1e010300011800381d95009020682c1c4140500421003071200380c2c1c039107614140d4400d02481e26000750f806810f80880070352294000c1c200444c0014141e031040701c1581c54001c49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 69846675 1250 69845425 69845429
    0xe01030f0c09090308160309050a060f110409090c06050309030d2c060609150306040f0809060409050604060602030408030a0c0f0501060f090509010507080f09100c021b03060c0703121104 82
    0x2192a171010800511030915581c01148000e2405000c0c0c050640c80d03143d200d40c000d12010f4880e503211480309202014540040404000c03c82401d59103a0b40c03032120720000c003603c1c0c108455070071100800169951240301500d015407598800f552408540d60310641c0102521410a800c2c095060800b1000b030727100c8803101c0070750310102015100340e10300f4000304409201c00034200710010754600071a00f5681c070002603e0f94002e5100c07415600000741810801e03a90f00500c0d04042e8400c0f400540420244416007089000318020794080c8400303130b02c5043c140d031070b0300031030040c0070301588244404804240304581103030010f030003822101a603101c0c0d80c4849003522803c4e044580b00c000b10b100c080124010300d07c14070358400c0c0703018020015410580001081d246009e0001901e100d100b5001c250640d4082c404210a028440810072606003600800f0392030380d2900044110411500007c00d0300d45c00c0100e0014030850b8100d01e06c03442c1000a0380c0645446108442c001c2585a4591080d400c2440c03032001000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 69847925 1250 69846675 69846677
    0xf0507150f09031206030b011a07050d030903170103080f090f0604060f080a1503032607020609100603050304050405090a0f1b05060c15060d0506010e060411040e01030f0c090903 78
    0x4030544241400b078074004d00003a1012400d40342c03240400114082614950544040740700084100c040c14070080610b00038280c0c060028009e284001d440307150947e0201c1c122511945a50714034114071080605641024030000e00a40410880c0d0901c003c0b04000500004200402c045440880c800c04920b054220b0b4100d0004a2401118411040e4104400304c0d8015039125090203081008241c00710101c0b41032000034240300312000c0d0040d48040a2000d1031348405a055950b010b890503440081d65108251911010740c02a200b402d0406d03891030007641c0507250000300551800c0e02d894140f00042000070f00980c034a00605889000241c1e0080709001458040d4001c0e2000c1d0b20070300080540c00c5c1940d0301562185000300300c2d48000400c00700713840c1c41c003200703c2c40c501d01c0654800e004504080d8401d0001015030064800104a84c40040c1025000e110251001c002e4140c003c510300300e1b40d03c100c5c0580144192080010000a10031014107003401d03106840d0321840c981e0300d127903d000b600c841510482c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 69849175 1250 69847925 69847931
    0x40c12030f0f110a0b01080f06040c0501080601170406060306050601050f03011401091203030b01031d0d12060902070b0f0c07020d0b060301020d021c0e0303011a0705030c070816080c010f0507150f 86
    0x104040400811031404041d202600450501d030b920b081100c4901e0cc00c1c40d060142940005107545e0292042460420451480c0002443c041c5004001406e0782d000495041e032601c008030341d855200d54240c0b016440095622442c42e4205003203110b0418000c402281009207450f008101d00e6501d5683c8052a03110382c802040d0030b8000400903090740c0103e16121030820704003002e14242440000c3c18150803440d42480e50036160b40c1c1d03520b000600401d800031907000d40005000700800c01046003003842804a01182600d6459110740c7e54a81e11a84401035440890000f43c02c0129020240c11600041c000b0b00052902c0c9040ad510000e0340c0001180c10241c0140c01c0540d0450106030041d40554909200a5481c660420040c003014000c0f004c000e4528240103e0a40d0820600300115110030250b08129030001341d8440710b030f0740d40c0c40a54040e03000440d03100b000025103100c0002d0012701d140d0141c40f0b04294019014088996410075002a5640c1003460031040100031544209606072560030300c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 69850425 1250 69849175 69849179
    0x904091707151107120e120f0c090c040305070e0a0212010905181f0c18080606130506010c0f060f05010b09041d03090f01020709020301060305040c12030f0f110a0b01 73
    0x2d4001c54552419042c0b01000411014000500701e19000c0c5c0d003e001d80c200012400c0d03032140411602d0381101c44401e03da110f1800e803070070160320028520288480454042c0026584c00c62640020b0250b44002411039100b5901800240041c00d92954440d03c4124010f0500070341c2001044a00000c2c0e00c4007140556403020f100b400742d841d1074222100c0b0030704401040c5000307503000340c1b40c00c00240c81e81c10b800c0243c7d03c510f070150841c400c01d20080c008440c545c11104281d21104219107500d41a6846480340700c40b00a081909080d90083c40e1040c10140c450210301c190304d8644040c080401e0343c003103d46958414442e041203407584141ea020340100410103440c0d0460b00140300c1103940d060700030040c0720f400d516040b24941c00007048074600e41051b01c40c00000c0d40c60710f00503450004903070071241416002100208410780c0c150f100a100d00c3c0102d10100100747d454200012800003040c0280c0001c86540d008048503000380d00c500540d181c0c900d40b14903050300d903050450030000c005a04032244541030b001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 69851675 1250 69850425 69850463
    0x1e0207030213090305281d01090302190f0b03010806090a030906030207020607020306090703021009080c13060f08031c020c0606090903042c0a060e0f04170307020a02090c0f0904091707 81
    0x180f025001289402498481081f40003134002181d80c0301c024810000d20114003031105c16041004003c00901d24240d80c6107446e02042c801da0f410074002c02105100e880700051640c80c00080e100405a00351f200d0b0b081c00e5082440032006075110b154242d0b0404401c014040068404202c114400c0c17040e003004d00002400e42c4100480e0960120001d0101304108609100c3c0d5040400c181704c10b0801107500342c602030317021100100500510391011403120705004000402c288007000408080500540c544004210001c52600702d0042d114100b20320381c4544002a00c504203000c0c02a041002030040300e003020307541d0b07d140783c4044401d0300c40800c5004403000300c202d000d031004000d5004029444140311450800702040480d81c0001c00d00c000103c02c2a0200e024450190004014101c7e000182d41c0c2c1c030b10301200040d41c0c07051003650480c068481840061034181e00355003655030040392403118628240c241001c10014101041c01075a48010480c0c0d550f8100c50301340d00528142d4440c0c0e013074100c40051100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 69852925 1250 69851675 69851687
    0xf080609062d040f020d0309080c06030f0601120605040203090703060f02090127081c0f0311040504020d02040504020d15060201021e21071e020703021309030528 71
    0x1800c1402c0144035240e400100009000034180b07014a6078030998482c1460102105004400f13034121601c100d0900034590300852201c182ea0b018002c560b0a0400141401250311088603035400c20719041022818030342c1f00f40f411044a40c0001e40c0400c84c1500c440006003283c1c015120f440b11640b10303110070401c01200c1d00801081d000c4038034045080145103400a0240c41440242d803082142640040186540d20100724000d08410b0045500e50703410b402a280b09200602e14090206840283c81c1840c80d1090003081e840c0c41a01200340d0a052034030701800007030f4020080000c8810780901c80420143c0740c0d48040c0042d14141c00c40400c170300580c80c0b170300810340324180c1002c0c0c11a40108400440c04e049580700c44207000041c1c00c000d80d00c16008030440341030b007a601c901c0036081001d00d00b4800c030703564000700d102e129074030151101410f04150740d020781c3c8d03815461200a4002050b03241c40c1042408903480501d030103011342045440c1405404500070000d510001440442d401c840903041a603900c42c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 69854175 1250 69852925 69852931
    0xa0b0112020f090907140d0f080a051209030406030509010203132310090303061d0c0d0615020c031c080f09070e04080d06050108010506071103030906070501051503030708030103030f090f08060906 86
    0x52083e5100b45015110234080441840001d07003554000103940086504c43c000705ca1094501c02c41d00009414201000c640f00d038032a22030040083d061401048044e64107108a90013040c407002400c0d500c0115544003455407800d600b038844048164020107229080502c90050301d407641010015091050f454050308441090f002035035641030800690072030343d03191903015401c404a0031140d034441421402540140216420428001043c1301a8484243d00060900f040741401c6054901b0112503e03401142413100c65078480010794103402040044102c055550703000000d200c01c0e40e248035201c0821007201c1000b50790444421200007040200c0c0402880748101414091034191099450200065170f1402860000780440010400c0101d0b80d607420406ca5005020107820a525140e660419034004e05049502e955804046401444d032031038048101d80c0c4480d80702015a00356401c42c0c5045460100e80c00c0120203010080d03202041400030350311000010054600100014a828400b80e42022006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 69855425 1250 69854175 69854179
    0x80f070c08070806040c060518040f020901030501090203060d1704170a03020706140a03021b2a06040b0714120310082a01031e020d0615020a0b0112020f09090714 71
    0x100040c8030005650701006d2089889a150640d180e282110300344003112007170a50140d0151400c03064908580040d00506020b0009880030001d42e03903190300ca002a440700b140c11a5014000c400c5400004025001a0724801800c0100d1410030f5150340c0d62010303a06040c092400d06a1100d400c202c05c00d42d0402400703028040c0c2c0d10386034110b20210302e92803540c0c1c00703481226024160042070090a90f0050340d001001c07908a0230444408100c0790401d544110005144034010070300f001c12551003418460300725400c480100c3c10307482c03400311142c0345d503022401001c003045258041c22040c0220507420b0b00145000f0088003044e65825444e1a840500d000c590301a0179042d00102c2070340c0b581d046c404d81c808400c072103003e082c0890003013400c81315400d982c0c4403a1240710b440761010035800e5050513140c2c06401500c001074034a03801084014804d903512901648e0051070040a130303005008d51114800d480780014405060a40c4004d464400510080700c11202e0511640c00303107000308821000050901880766003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 69856675 1250 69855425 69855433
    0x3020f070209250e03120703020f010f0e0106050901081b06040312050a0801091e0c020f010914010506180406020d0209060a03050412050a141602060708030108150919080f070c080708 80
    0xc2e54005c01d80350800038403212030310407011800200f403500900c88035424000c900003c2000d0818445030300000c10341201c403a0aa586030000101d03480c1080b880c80c505a0341614018070381c1c039103540b0321721450801c440a041d0f0070403070034400000010000303070300c24002c0be8050701c0355515140c021030001c08004050388041c0281d03041c03100b144000c40d01101c06c0805102e09060115500301405026490b20306000e2244485610b0301d070302d20b0140800b00e8000c21682c241c08000340446d40300c0000f0443c100c0319100900220707c100340081000152940d006081e400d040c0007016040c100444001905034002240b0480465110320410040003405000c0301c0e80e1200c01d00303003141000c1010314020003400315030044043d001310004550038881b4501d610864200c0d4028801c0c3d80d01c407900d1030240b549820a00c92106940315402c80c00e0004440b0702c241c0340c40781ca42880180a490503001148046005840c0291211501006100613407070045005064a5000d00352400c125490050161b1418016501812150b04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 69857925 1250 69856675 69856697
    0x19110303070e090a2703050c0f0705210d1d10080a0c08010602030913060506030403120506030a02010c201e211509100213080f0a03020c0103020f07020925 68
    0x88017a05000341000002443c2103048154681a905449111001581c52052041022080d000040c9107019503c05030703021800d00e503d180c1660310825a003241042660008207900b0401d6120325504c0d42d81750501225042841040d401092042c5920071788080062501010403d12440e940038403001809545069039485d890700f10029240d000e16880c4502c5600043d0000320049402d42109000d818020200d60307407811b040c50080c2004d1708481c0402026401c2a00203440ca00e808508014170a406860b000880e81465654100c00900c142c18041c4400d0b440c0b824202544840701410304e000c0c0716900c401c241822103020443c00424a80c55420b07207000d0b602402100c68008915800c20100d45810b110140c3c44482145040200391490b111401348082800c04650100100d4107007110341440988215161500c0c0303035500c501701a4030113409039122008100381544668014610b181c2c09140042c1001c05070340c006140d80d03405881d00b221a40d02403540c60301c080d040e03c1007844040503e0034441c80d000f03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 69859175 1250 69857925 69857951
    0x1180f051003060c1d01270e09060106020d0e060307050d050106020d03061a040506070807080c03070209070203130b1b0f0a230c040b04020d0207031709011119110303070e090a 77
    0x8424400a0412440030307a0b0029008041c0c41e441c0044640218420035544c0325040d00c1162032027181c200360f4a1040c8400011510700100e02e089a061082d40d0301c408c0a070b241c2007800100c0d480a40f404042050800c0f11502c94400742c4503681c041c00d0158068184102000c0b001025501c1d07681010090040d07103512104000c234003004507403c1b18819a00d03075840781918104640c040c0a10745020303124440015680e51a1a0080010b12801f8422a1100d4054039102c038200e03568040e02c0c490811601c0d0208050011a000328050b10420040c58201d950036109001c4090802c0300c004036405442d0b1054038481e040001c1d02e500b00040004041e09940780c1080d1780d560035030304c041c1c03124294000d40c0e5503d40d258041e1900d8040b58981d4102d10000d540d1840e42c1e207801403802102600b0111554000c40200f007055030107000d0300103042c5083d44614107050b600c6000c0702d018421000118240a52096400341c0f801051000c4e6100e00da040e212080c1403442c0109200d00303c1c03002068403030b8803072030011100d60750 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 69860425 1250 69859175 69859217
    0xf07052a0a050610140d050a08041206050a0204030203030304020f031c110d08100608070201060e040b090f0303100317040302150a030e0c06030c071407080708100203070801180f051003060c 83
    0x542170445a45520040d241003503401c0c200b02c5400a40460000507000c54003841410001a803148206010425903030359540810407070085010003541034000b0404035002d403503c0740007080004030007410354604240202e1140d1010441740034080102c0c144c05d42204481c101807000105900507030500700a14a041c91200d48802c0707660140340203221011b00400c060700c2c801d50291018201d51205c00200381864202288450011140044544502690340e43d210b140401a80e015024201d1150829170440e07843c0304d004883c499041d0b0041d04280000005a51030142a42494451400b03003540d41c0303100480242a5a4a01c2001d40180d0118603088815120801203a500844889a0544a01c40c2d40780074818a030116500d81c405108078000810fa1420129410003200c0010b011030b449815551a500240c0c00304071501d40101e0040401005525000e040c0c110004606250028201514907918022140141e4544408131503a202c10b004200403481342000b020440d0074952101b542c1d2001680c1342c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 69861675 1250 69860425 69860459
    0x50307050d0210031404080702330c01020c24010e01051806190e0121020d030503041707031701120c1401200c01170f07052a0a050610 59
    0x56669440040f8101d0b11942c070600050074404e019940a041c1814201425041326034264814107240000c51240051605949822a07125003104a00701c0c014024a4040d00801c189500b503540030002d480f1000e13010b0002000310b11000c00e5009903c0c1c01c3d119400711200050300b1402c2092010ba00500c40d95a440d070562039406000350065000d0b50760480800c50203484554a141544132981000c02e984c46413440c41c906840c06c000b440c00c68951912442e0b90182c41c0448041e40101c641d07042000800c0c400d42c011a48a4051a030a40c54031103c06d01c0500540c0c0850801d4001600c100c02103411008610400c0740106a00c0041d40d0b900d900c07980300d081801c030191107501038904c1e01c1c107040c10499000d861005d611001c0e040b1081400c4805003030141e140d12000c078400d0700041d0103180300c590482842005501644130786610201e261390b16102a25960300a194503212906007407118076140e24550701154209003081c010f0500700c0c0c41894118a06030000e060000c1004100341e0a120039440c603841d4000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 69862925 1250 69861675 69861679
    0x606220504030306050904061a030d1b020609060d060819051902130905070807050d0312050c16030f08060102030c0a020105031812040314030405090708060a05040c020c01020106050307050d02 84
    0x14181c54626040e00140b809134411900404500d0810040c044c2650003803880d203900024550b030380144001056101c040c610030031004180781c0c451158044c14286140c0c0c645070310103440c55180c0580000007540b2604440c2c103403070200e1744402e022300c0071803000d120030000205001c03080c1050614540e5000e49402c80d0000300009680303400302d00c8040d0f5035009164900d440c0300744001c11003035545091950301c603400303401400d0051049440000701800d0009205681c1e54265031501c1100e01c603885903030090310010f03101440c4500e0a002240711a40030849110b10315219031034100510f21506009010303284005d2446041d50024850072070b104401141c502c881541c2440e10584c1d13075490000b0300c480e82901b420804070714840c0b0010465000c982d0b034020025a8017950140c00f4400d5507010283d0340b4801c501440303410102e0340000c18201170185155035000107004006004540e1541c0204040354040000034005a212070b5212400356028882c10018100903000b0300800f1b030421001c60b0400085c190000c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 69864175 1250 69862925 69862931
    0x60203040b0301090c0903200102070b120c0a12020d14100503030d090203100f05011806030309050d0302010b0414061305060307060c03050c07151101050906010611030c1905060622 79
    0x82d45e0b110f40081c00186a1041d841820420084048050310702040141800740c1705080e0302184e0210150141c605041440c100114143d03a56090340a981d0000040803003480b00801010a101d011800a040003100200340050070540341403070040c3c480c201814400344900d0480302800a81c4010040720301c0f9117580d24000c9040c0d01d00d032003ca4604607423400407501c100d19156141711510941d802542c100d42000400c0b5480010703401541013296003920000300452039005040103142031840174900024024000080d207400305030701090681c3c909504030000034030b184080203075a00c0c1680080c0d99070703044054200034918040d80800d90741c0007240500000d10011000d250101441001114541700201c010740d840c0ca6900c0c541200001e40c14038180b004070716254150300450505205c0d40c1d104440c25801051240d190460603074140320a0360440c905400100441c03004028108031044406041e4207000711030041c607040c1b050030039402a040900c5001e524030800442031004006443c0000880000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 69865425 1250 69864175 69864191
    0x507030803060a0504020c0c04060b0c0a0201030b270f10030c120206040f240503040b0402150c030a0509190620070513021801110a0605180105010b040906060203040b030109 76
    0x2003500f240c2c1d5004030350003400020740703080d0036031f0209054000c80b40503a401c1c80041c0d00d41d04040018003807200649015407120300400059031080d0040b0000c02005049107001080b2400c9940c0e41c02895060011841c1c1e01c0350522400c4140258004e6014114180b03090316203007940e86805071038a042c410700301c00440000c1d110301999943c8084500070085108004901540c9528600006c01c0503c1d010301040c1a014201616500410403244247e5001c50f0528003662981c0c00c01071500701f900400f0407190402e021000070302208200921f041d10f05511802c0d20b034008401008000084604100401f400e000030801039a40c0102140490a85502d191071400702e0203c07580e440c0c0281544625070090741c080040c001c0c0c1482d64000c000610b030304002c0070101211440150b841c0e03100c1d42c3c3c270081c0a901c610310550103e43d090780b0072a0403124042103580000c1100c11038038256442a0003000ca080000030301000680740c18450070004103094005141414034107501c001c2036010501c102c0c00011389078400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 69866675 1250 69865425 69865429
    0x714060708090312041712031501050c0a06020a0e0906060f1603030e0102130501080f070f0c05010b09090c0102150c040306021605010f0204050406170a032d020105150d050703080306 80
    0x101d2055100004041511196070b5181c444110158000070340c441c1c058040040e2246000e80116071181d0000100e00c15102527200046490364007040e4804800e0184c80c07400c20000b5901d0000300445c0341c261b61000480e840b40f4040041a0001801141c85042c040100140481d44170069429075000c0d01c0c2d0f0b01805055904054001e809d032115407080d29480000d4541d039901a001a22003580c81c280e035170181c030350b490210141080400740c0745507001c2411210071800d101d10034030035052650b20890011802a0342c00003c90300da84010b84840180e0381005003043d07d42d580c1049220fa0b83c400c069031b05402070403c410202d402c0d00c5070380000380c0100d0700041c204142503403210594581075070000c0200408501049201d000350068002c5034401e904200c40051181c000b80c082d0480c0701e5000000e400d0f015000c1da000c0d503e07012002e01c20703a6441c1001056101003804070306030320904405500045898680703a1400c4403c61506094a841900107140c0c1c1c0010400001d0f006043c4c0350f00581956030713030b01e071100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 69867925 1250 69866675 69866683
    0x19050601090305070e01180b0306010915030b09061e01030f121103030907030210030905100b040e060a0e01060905150904030504050301020c0309030105090102040b0f07031209031107140607080903 86
    0x5095441034444c001070301100082003174100da10040f081101c0c2c580c950700b24416691010b4180c1c0e4141d0000c0014020706007503611102612070071000e900300d420b540344d89420405208542d20401758100c02e041001001482058a4601040942a84075981540c0d2280e10399800e2000141104008a235400c44242c050034100c143c1c1510b030000c594980c5000c802140e61000c003400f003203008282c40720090000c40c1c080d0241f10f0100b0303400809824241d0b124a1100c1c0140702c1d4103d202d034040d0b110906100a1502401041d02919911501060810b8000b80c802c0c2918815446950308034640710030010030140209001d600300b04119010000da0301d460034201c803076000d6500070b07a0f815440000c81c001015400030043c084900d098000b801150740d01d9440a080f40140d108050386044104880001050060000c203111882801c1c214100c200004101e000c403007020108078041404101d079106451010840140140900ca201003017040c28200854114041c10400404514001c40d031784050b9a8248 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 69869175 1250 69867925 69867929
    0x30e0d050c0c0a150e01090602120c0c090c0406030624050c07090c020703031214010302100201060b0304032703050c041503050a0309290403110d210905091905060109 73
    0x2018511044e40f10501d80760703006850780e40c44d0040740b8558011540c0c0d500504070802161810780243c03201c0c0d40d108402d10310303580c01a006140c440c000c030365401d0125958400460300550340348100315212070508402030101c0b540e40d08200e040c91421880c42c1e1405c04d641c0312020130200140350054840c0040c24101e460060542c000d101c20034113014000c021180d00142d034804803030095a682d100c0c1d240d190301d20407c50300b0b03a50f42050704504980041c03015003000348105409511510000504598405081a9a03003059404400080030440e070004200c00d0b5111903100c0c1422814211038051450380d0340e035039680c8001c05280c01a0b4540a0032021803084071100d50081d500001a10000c010500e4002c25500280c05022140500c50070088821000002d11090f511002c80c0124500350464440d4005112100100390b0f204000b00e100340002529408040c00400580c6041b4400010b0340c240034054115941010f0f00030464202003000d000e281e40003d00503070f407c0900018460300c03a42c0040360301070656 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 69870425 1250 69869175 69869179
    0x12020d0512090423011419060c02040b03030a200111070b0717010b0f0304060b130608061513020c0c0d0c0602010b0a150e0f030a0501051501030e0d050c0c 68
    0xc90100c1440d403000704028200d00c0e2044a04000800504240403854050401c050111820760380050254207a2101c000004800090055030440407144180407884201d40103280018800880c5c441181454055002c494070708a0180d03003400320150004040c0110b82e6001010100041425044840c00f0341c0100034000104032040d649040302d0900c0341050b04191941c40005900014668211a50481c203505849017030502c0c62a05502846c8800c080d00301500030b4905a83d6100410011744d14814011008550380c0000b090151038003101d6402c010000b06030810745082e000e24142c0740d5a41206900080001e5400140c6484844201b1450060a1418907811104c3c5260a905000700250030750202c2c0d40d5603000744041450034050000240651150929522070040d803020102e001d60030050030b004001c0e01c420302e00824000001d02d40a03a089c010348403a5922014003902d800822920f95034070b1003e003001c0c40b00854501106a88924203000c82d82006004110720400407003e03c004044d00c680 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 69871675 1250 69870425 69870433
    0x13020109090e0c0a050a0b0301090207020406090c020604050708010507020706120b0607030c150b010f08040201140d020a090503010b060922050a020a02010c030b010f1404030b0702011b03060b030112020d05 90
    0x284800d850b95683c5000240c2c0e00c500802e550000b403a00c1c0c0707005c4090a45080d180140d055910301460302e0040d40104800700e80c440d445107000305259035603110b90f949064040d4010300301c9040504099080c800d42e500b01204503410700c010005c48540006000c4119901d80c81d000c1c0c040300c5108a4100105442c4619961040000942000749907000740c0090006010312140004d4a46042161003110702070b42045010400040c40c040e900c0d40508016a40f00f80181880d6250f0710074814610801d82c0105d621000c07103940480c0500100d80d00c80403c0015050650017004050307060400680f942c0500206581320304852092040200c81d5031003200030a0400395402e01041c140401e6000282d004213080c100190700e4400300428641c46400340a0913142c040e10b0f15861408101400c65410f1a02c0500c129a5007003000700100040b521400e00e03100c1c0407143d0000801c148601c200d01102985400141d0030141010014807110b1400f40c1140d04450490617010710b1178031281b0200d02041c10440005d07001c3d000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 69872925 1250 69871675 69871691
    0x120204090c06021c080403020c04090503090405040501021908010e010e040510181203090b041104021204050309030706090605030c090109030609031701060908070504050a0209030303040c08241302010909 89
    0x80c0000380514013078400481034040410380c4004503543e01003107502030010b034006059025a414a5401059202e003d041540c1c038002d03c4c0d10104082d03983c10b44048540c0ea50004160512a42c0c00b02040c0c1d80c080325250a00d45545410a030352045074040c0940e80510b4544008241084010000050410401c05040c0801c2c0e0f00c036080d0007200c42155109a48584000015403400c0780319100d1100303155442030244000b6207480d1075004102d210381d428039421560800c50032204c1c02c9448540e6105074802c0004550303074401842410b040c24650b602c41414403160070000d0002e9504071382903c1e03020403503003101500c0700c80707100c0102c0b442900c5501c0a40914641007440c401e0540c00014245041c0801d03425001a0b47d03100310481d20035100d44144805604041818030462801d40c00c03142d0012207651000d8281001040040d0840d8001c3c0c0e0b04580c504640c0008120fa40307001d019440f48000300c2104407540302010140034000c04002005034800c0c0d08031104013011603000c0c1183c840a41350301d440402c0310030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 69874175 1250 69872925 69872927
    0x110d0b0708011a0301121205091c050c04050112140106030c08061501020606010c0f020622030b010e150d2a0503011803020d051e0a090509091501120204090c06 70
    0x5000b030251030091080010655103160242080705d0484400c600a100001019145d00014014004640c42084010030111003140c0d60681040309000c22a80c1d0043e40400a240c81d920301445690b08a000358240001003002564103294002c055401c402030300c0c2c41c450704550b120300400d0250002451001c03030b00000304500348000f0310300f4072030b00002c2034610200d070314a0300591351100102e94190000d0310208010000600a5417403c07040c51001d085903090042144c0c004054250898542c0003480c0c1101c3d0400034410fa001c5c00e40e0051154090826850400c032842000d502c824001d100d00030b07a5221810340401144540d400c0100012500c0194003040f10f006140c04034030035105643c42507003807403030214002e0844000c200b2165455001407000295401c401c2d02e803900410a046481e41c41c2d0701d01d40d05a0718108008002a000c2e83c3d9408803428145010081e441c50302074038244c801d500101c098101c6110104000e0b0650306c0c1d40420302c4140b00d040c0300040290244c05070043c4421041c040c009911 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 69875425 1250 69874175 69874187
    0xd05010b10030209180c03010618120305190509090c0a0507050a0c0602010e1203011509090e060a050c071205090303071e0b160906030f020c030c071403010605010c110d0b07 76
    0x101404540c02003410b50024240c171130128050b11100e503805400c00041040e940030721000908680d03151103041d40e40d0b07130b00c5200302e2400900340c00540c00b241002a590f80700d0041002c2c100054003507400c00905000c5c800b00030800f0201d004003107040207000011400b2a4a00450644200a44c4141190300b0500a464140c0d0505114403a001c013542c203141061b402c1c17443c0415007010492010f480581503078640f044000040301130100b0401800340e0300c0b00203c1c28100900542d046004540000c065605000c0c02e0002100c00007400001d201c0000d001b07400005800400b02c4404108918005485103400e4000a0451084100040840d8030f0307401900c84114203800b141701c446011710900501030340c039000d6a030040060038140d4000a01184018801d86000794003071701e80d40c00300050060401d01540d140515507803190300c4205865001120400451b454283c030f095424400360000e0001c1d5103001d002800101d41e10100810150540250320125142e50124920594004040c0102c6050000c400341030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 69876675 1250 69875425 69875437
    0x411030711120405010509040902010c0f0305040812031e040201020726190201020a140a1a09120c0705040b061326010605010c2907030b1e0102060103020d05010b100302 74
    0x1c1d50180c4400003031110b100d941030300c0c01c0720410b85a803803030b01c00f40d4000c0200030318428001700e0610901c00d0a800200b104001e01004542c8a43c460a0f035503402c00e445c0501c1e1000c410381e00d4010740020810813400e074050410a58502c0d1f89040003a03a103031260710043c0e041018a400035450700c03459102d8066240f0800b0404042003803c54203542016458803d1305140d1864920040d001d6482140366200144413400c6942803102c41500351420b0220698690804610402d1003c007010b10035000e000008400788048280c10789c5400c039152804100c1101d01c4c1d110569840313014440c9540d4030300c0000030340741c8500300da01400c07611241c402119101e00040b480c0d4510311071002401080241e042811010520505040d00c40507102c0380a40c04940e519504c1e080c0100c03a02154000030b403000020241200d03c406801104203840100e00e45200c00d0900c1070001d1a400090600f0000e20099080307641c010800c181981d4064690210f80e10303150815a014013124207440360081707040051440703e150f1550117440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 69877925 1250 69876675 69876707
    0x309061d0a06050c03040f1506090213080105060109240201110a0f09060305010f030b071704030306181506050f070b010e0a18020a0509190501030c06080106021902040b04110307 78
    0x8a00d40350300c07080320010300041b41c0c020012852104103c1c04141401c2d0345000c036a00c80b05000c0303031580d141e903070350800c5c1d07005029403881c07501c8440001e01c940034003070080320340c400000e207001264203141420010f06039044140a919007180035400c050350a2007900300210076501100d903030f079840000e244000c109405042244000440c030071808a0b52907c01c1c041c09040741c0c00170b5210642c0134290b40340d044d140e48016103500c091068000d100300180722020300d01d0b031066000e0746001407007a24010001020303021300e11010108516025a1302c502800d02e0b0301c8c04098620383e06d03005841e119194602c11941c4245003001c0c10440602d00002084103806607850320a5001120500c44061250320303210031880c1000c03000f9400030440384248070704d0820100c0594004020024401c00740c3c44200b501048500030303041642c0d075a07010b1f40184603460300900c0b85401032000d40b000345444807400c000142d1203040084000d10a94550020f0380450342d82d42c20800c400700708219416520700b0140b1000d0100c0035117024030300c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 69879175 1250 69877925 69877931
    0x140607050408030702010e01120e06070207080307030503011205070f03051006210b070909060f03051e06130503250c05060c0312090109050f03030a0f05040c060309061d0a06 76
    0x2542852040303040c0c1d01124051030045062410583c01542e00d0001510b10504010380b071104031a03207080a002c0c160591081c0300203011a03040480001382018155084100380e64003c220100009030f20104490440d404d1904054030315038103151143c1010140d44c000b943d104441600842444004a191a81851001801c1044642d1002d4030040c1e00d800e035082c0c07c541d01031608043c0108002002c500ea0103c8a80340c1800308645822140084824a401c4034000d55003008013481001002c1020342d00c0031a82c0620a00c0f41200e40e45600c5e66650020703c640c0042d41d820f00350100300582001a904001e103011005e1003041c0203540d044104c600060400d070380d100351040700021f050415000b01c59a40015001461030200c60b0710b1452a001409410f080d003540d40c8011110101d54144040c0110120410145540b414844860070030307140701701c41000c010b62a00042c880021140c003840b00c1110310358100840c3d801103030304080d402004c601d140c006103111a80d6158031400c1e408220103842a201d05010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 69880425 1250 69879175 69879181
    0x402032d040b010308030603120f21040b0c07060e070e090d181403070f060e01140306090a050c0702040912110c0d062406090509010501020a020f06090a050d1406 71
    0x3850320003401d030350140c0000c64140040c00440d82600046900c071401400f00c41c4412002501c0200d103900c0b90700080521000410440024841e216601d0407800b460110810740d420242c484201029002d00b030300480348000110302301040016000125110007210942e002c0c00d542d0181b00300034903401c41754105c40b17001d43d2000709003450280c00d000082a10180d4200d0f807103828103100924601d10030408170742c1403182090005508000c0d03034805000d03045603135401c0004030700782c8005030211900c0b406050043e181441006056110541aa588032150b00404103142c0c640d00c0c0e0301c401a200b408800b03500702c0e0070000000c091084061025040103180d546094107420040045512400d80403042075019074100302c0e110200b0001e402c007501405070b85404e00c0580300d02001f410308a4069911440100b5460b076800c120074541103c0c0301d801401c00380007800d21281e0715800150010507440056104000215100c2c1c80c81e00c4102c19600980000381c2040398004450a0000001d0598490702d0102e02c142000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 69881675 1250 69880425 69880501
    0x106030509010e211201090f050709030506130602090405040507050306090a2a0807060210140705030415060f080a0c0501020d02060703020a03020f0301060f1403060d080315040203 79
    0x241d60585041d80c03010b0110010001390b40c0d00d03003030001040304030420740c24001501d404440c0f00402d4000e1074103000c00a02c80c0c4910344a40305980008007031105200c40200c040020540c00300701180c0c80f05901c1417031401e13000c04d440d1000081c061554001d40180c5071808100810a0004012080e54022801c80320300b50b442500981d40c60540040003424440d07441006a08203411031041000520b8024407402c080c2d88500c903041c900082d5522010042e80403542e062107408940c42400145900c21581c142c8600d008a8040c0040c44040c0c00100074012006103942c0c0100c480e80440054030540c81c28051031507440321425618140341e0020340d4214080e8134005810b40c00040c850840240c1500501001d95616906400a40200d4050f03824107408102c801a40000c00780258041c00554988049600d0341c1c41300141004218498214250810414040d0356070369442c5581c03001c0d43c0481003550f243c1d503041140c045032011050140c3c01c5800401400703030001414640b0900810004102c210344103d07290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 69882925 1250 69881675 69881681
    0xb090a0b030d0c11030624040c2106030b010b090a080106030302060103020607050703050a21020c01020c150f0d05400318080303160302070809040915060e010603050901 74
    0x39800364103a00940e01a80303a5400b5440344440031380583c80c1d0010804042c004039040110844a4981824414100032610b1012454840842c1e82c01c0d101000000003250020b00888880150501c03450904400380114040c241c1004000c1c44c0c1c0b00003800c2c1107594900c3d8692064010f01c541502c641c00c040d40100c2d10020500c91103048030f4050b03008121591035074081c8181948075801c02c0d54540219080030003c10f4040207200c81d0540700b522042258a2200c40c004d1881000c41000310464000b000c5c102e500d40c2c0e0008009581d48000c075082c00e02d09401b40340c1480345209440001c4408000480c1a44200e00507500541c42190b5aa58a015040203103842c030020f24103441c001e0042c0e071520b146110061070130a42800d10701e40700e03040201c42c1d0908955200740d05801b56000103010341c000403c20500c6804086441e213029280d04065050620076980c3c6100350086c180f081e0b008558a00d010001e1000b0f50b0110b880340e8000744401c0113401e0302ea00030721080c400240598404a0b0909012501680b4144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 69884175 1250 69882925 69882941
    0x1401060608100605161205040b12060f1f080903071b06020114010608010b030c0c010f050907080d050301091104050a030609030f05091c0c1d041b030c03080c07030c03060b090a 77
    0xf031540035998081d03030b0748402200c010380d0020101f080504c00810041d15607001843c1c04120b0f503400e20528a8003c003048841148048140c6c0140c4800b8858005c150310340c0c401543c1c080580c00c101b9001d0f0b07259600726185000d4580c02528061095540e01400c0403d0280e440950300c40307500a11240d03020314440059420300307104180001d03404d18010410200c1d0040910780006a0400d01072615100407030260940f48491181c6400303030703079401c07c1c8820b00b04200032440050081d18054140c1180d41e120140640c001440790001c01510381901d82d80d0607142000316009000c000b030007411446c0c3c890a0200084c01092000c40209454100c9543c4142c040c9055600c00003006010401103800c4920b592a500f00c541000c96420a42440108500000c5004401e02d03103440c503107407034080c5014107007001d1900300110030b11000e8507500720900101e00c044824030252030700b206486685202d030075401498a09950300103007044d440840088100b01058105e540c00c4031301150b030350030161124040d4400b196080d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 69885425 1250 69884175 69884197
    0x10203160804020d0206040b0904050610022a03010e0601030501050903040b18010e03033c030c071106041701150501020d0c032015010e04050a02010c1401060608100605 74
    0x844480c0e44a074550035402440507041460211107a40800c02d1a0482d0300312052041d00482c20501030706141c07041a0b886441194a2400c1c0b892400c0080d442c0c0344c0c4084518250b00028003035041800c0305445039002900302070002c0101110b00112030b900c49074280011180da500b080080380040f00004282d80c19241c15041d1603252401350303a50704000690521406047c03140e246061b60855806201400c440340760f840785e010b40342c1c07080f112904601400b1112152070302c0740c8800104c04c0c0c0000405503079009074420541c541d40d1449041c001102d0568190b0141d2044c2c0c0041c000c1160701a140aa0200d841510f000b4000d1041e000e00c0742500100d603000d1140140d00c582201d02a4612807509402c43c940241012000d80c12881d942e00c29003503030740308051595030001ca04c01040d0522003403124010680399a08d01801d04156a0303447d100d0646417406410007418498540030f20007048160f10303140720084001c0007441d40e50341010740044000c54109911840e4414001940d0380914100c400b0000c0c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 69886675 1250 69885425 69885451
    0x30702031b0f1309060f0c0207050103050108060f100e0903071e0b07120213030501060608010609031a150303070f020a06090308030a0f0e0f0606131e090503130e100503010203 77
    0xc081d00307106480c0b40100f810481c5a4650014402151241c843e100e04000c0300300001c2501984900042d18000a0f644464100b6141c40010069003401003480358001c002050400800c2c2c0740e415078500301d0310103600840c880c846d0600500c481303030400000070304200d0f1040303e41000500b025140341811208144020f02607031403210003d000b0511400400784400b003003040c014103045c0c43c140903580040c1c442d00200c92236951000107001c2c19030011305041c010300e65860210080b07803c3d035540c580c0c071103040c80e41d000b40c00054002040b403000e0300c025070900f090400b0f0200d0b61600c915080c80300302c000151030240c1c06104282d901140052245160038196604000550302c0c540704d001d0301000400d02d00c1e619601c401d694101070300c10128244400100781e10702c10000d00d803500708841001201c02c98101c42000f1985000070142c1c0c001803203160384050481c0d10718001001000c41c20b02c175045118281090080503902000800d224079041d49490013a09011456408a51190f0031f16080f484143c0d680e00d105c01c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 69887925 1250 69886675 69886699
    0x30a020405060102070807030c080708070501051608040b030a05040b0c0c0c06090411030708092b05030721020408100504081b030c0604120e0103140a09110a0305030702031b 76
    0x10540c0160b034000c001807044661265403034403124106007664000303d501c040403036070802102d030007004524080d1203000054002c0e41c0c90036001810501c54003108140b043e41d02e11b55031060000f0740c01658002e01c1c17450440e9641e4a070944146000700002c580807a288100c01021031891440b003030130ba805620010b001000b102c082c000800200e60040740b4010352040d1074141c0d1041c03100004018600810554803100743c142090b000d00b50038034001c15141d168407042c0300e2080b4540c0904443c150b1070030056080c81da83c0c03500c0d002d40c200c500f180813a060404a29580007400c0684080358000c1049a500c101500c1c065401c10b1481003c4e24000d8401074180c6109020045d84602a920b400d1100c02c2c804088174604031041c80000c2c10410112010ba50700c1c005030701c13920040b030703007255402e010b13030303e00340b030104045c0004025141030040083c040c030305516a80c80d500020419840f0400d40012801400d81060583d6494443e03640d90102c0d000700d00900030400f90003256007441003001c0301c0980003000b44501c54 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 69889175 1250 69887925 69887929
    0x51009080709021b01020c0604030f1d0103050c092d010e13020f041508070906020c0109060305060f04090b150d0c14012007031103030408060a05040204020c0706080a1802030a02 78
    0xf411100003d4401390b1446000c00419009200410800c601c0001500c1c26142c2410040c000034a21140441800050300b91628182e005041c00d080f00c00e424200028503850780704000b0b01d10301500c2400398004004e03a83d101441d00500544105203540107503151a0b1144410044550014003001113400a0080d00481800300050300940030700303070400c0c01d550309007951071414444022402c5c9541011031030302d41c1800a1194080d04400103491103000810358500f202d4002040c0050a05c604020940d0ba5000300300c0d950b440d0482c06000c0c20004000b07000c10360450900d4283c00c130003a0f0b15450007842c410032100030307410904100c1c40c03201d410006044000c0d18100c014424110070001d240c6c1045900045d00c3d4038411080030794152200c5003401000c84d6411450308152801c400b40c0101c1c440c0e88284020032044000040d01c4d54070492064000c61540c40720310228000e40108508a455402540d0020807240e43c0003640ca84128807a400600c589000d803002c4c1c046c0d003030341c82c040030303400d50080389031788001d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 69890425 1250 69889175 69889177
    0xd05040b0706090f0c18060603020a080402010e19080102030f010e0103080708030703060e0108010219050306060703030e0703051f0f0b06030402011b060219030b040606090509070311030a050105100908070902 91
    0x443c4c05000d0380d04c8004000c4d95001450b03401c43d0004220012081202408180907104100c06852941821807401c0800900a0401c040050000b8100660303100d0b0f080f550b44a082d900b0b644403440c20180d032046501d400c030300c501070740003200c0100010803034900015581d0003000b0064101c0381c021203424504400c07901d6800083e031005000310141600c440e000a0b841c0800c940c018000e00b510000181c40b400840e00f5500501ca810704402c2c208031080c03041c031070380e40e44010440e10992b0745030600081294061a10ba0300b4848240d1026005019200e01d80c40000100c5480e0462001e441500f000600d001d8040c0700d003205c2c0295200c0380c04c000305000140c0194007035059481c42e42108035045041c03c0c441d40d144401d99011110042d4900c003000a41800c80e40c05000307840809004a40500c5602c1c10030800800d030081d580b141c00d129250043c08103400318000e601101c072450b40f26146a96a00c0e058210030043c180c05c0c40f40c42c0c064107070200c028415500c41d01d50442520803400c00b8102070b51400640c41c0203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 69891675 1250 69890425 69890441
    0x609010e0714210603010c0e2202070c0602060108060403050a082806090c110a0605060d05070f0f050303070c090515041a0418081e090d050705030d05040b0706 70
    0x24410555402c40c01d0801c0e4001a190b9100c03401c000744503010030403c042c101041e004e050207010380e04110891900382d406c0349202080000c140ea101070402c0c001040895500110002c200175644001100d41c244802c042950003501d495400302c0f812642d031042000d41c0c4130b10407180540000c0b410b019024013503100380c14a6420400701800c981031840f661071100d01d2204654008010140da4a0040242400c3c6004508034829542422000d415104c150b041c4c40d0303401c4030001040d86507128000345080e52690540303509141c0081c221000d098031003040700d0110742c00e40155841610340180001e814900001201c00d1160300001520b02640f4028000340601005408a02e002c40c10451003401a1160b220391501600c130002c0050b150440702c1305200446410803140d5410a40d562000c101040c000001c41d032580e0141d0303007410303c40c607001c1d903004d10799008021040360b101d41d20901510511000190841c02e40308100c09a9151034001074095525210743e00c01c610140d60184141408119503500500d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 69892925 1250 69891675 69891677
    0x601061403070c0b130501060510091509030b28020c030a1d03010e011401050a05061c0f020f030f0c090a05090a020c01110315030106030c09020d0603150e01140609010e07 75
    0x60803266903842030130a85040300d07000c1e034400302a01403078244082400b44400601065800c030014407803404000700000700318090942c9122503070500c07034807042c441d182100045401c00303401882030800203a5000e102c46c2d00c15440020101c8200001c01868941c4221250039111200861a161504030151008290036080070185400903040e628262020302442481d07010003000002c0d40030340405c0ca40e002041c180c204900030382000f4014007264448108907420345841c130b904140382c6c00720600640042e1900e004112011400840d2081c0010807480182d8040c4d4445003c80c02c059480c0c141580c0980642183c6c0e43c3d014007202c10800c514184000034941040c0800400340c80c000c1710b0300d00c650940320214203502041c3d07000000c000f101000c035200420640790460091104e18a186c441801c1d28006014080003e503001440b12070300c1219500c108021b40d032200d280f10501e000050500020059518003035869401d1146e0003900309090004148215001080743c5410b900300007800c00b0104000308018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 69894175 1250 69892925 69892937
    0x1a040e0601021513110301050a0207020118060c08130b04060f020c012f01111305010f030603030f1b06060b130909330603050601051041070b04060b0102060106140307 73
    0x1d4840d44023030040c2440345400b414050390760016031000501c0807002c50701c00308c24a41030f038a092050350381c00302d80044c1c03241d0022007141d114056071108044100642e400352101103030014000401d50b401040e1444808140c0d02a00c00004071038005590010b84008526079040705480600c030b0a00c480b41d0050780c507031154000000d41c0000b8604000141c1d01c84040c000c440a50254100070560384240b07480207100399464148001450b646d005049101c075089048103005400000310071601440102015464000800340211a622081028aa80124100100e156001c0408035100c486402440c0240b6170140001120140b60308041610345190885640031034041c1c801c3c000d920421f400740801031809107000e44038070f52401040101c850701e003803582001c1c0110a08254074400c54004140e00c401c2c8201607440005007415422080d0101590103143c2c062030201d0380b0800d002c50080c0e910712072803081e042000031150141c01640c1d01c0a003480b581001406440c0220107001c606005103800c152182401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 69895425 1250 69894175 69894203
    0x506060711100314011403120c0622020618030706030902030309270a02190309051b0604080d080907060801030209011202030c13050402090f06061b071a040e0601021513 74
    0x7855849800381d2000712205e84c00b10b01b10000746001c0c002d00b1043d10712400ca0320f1503c94030307030350300c07901c40b400203189010031000031680c03117900c8020000d001100b650052003248c1d50b41c500c80c44003050300e1401860324020310584201140c02800b80c454940341300e13001001142401101d00802c148003c407204030078800404801c0c0d106502c411407003020b0251600040141c3c445041c0c14020310b00d44060320b42d44c4101030500800401280d1701283c8020791035500c0600c51403a8107220302141c01031042e9440a2024401d03ca52070760196845207007107000300842e000b5101c8850b92901e04807103118007800041d611140329401045a4209003400d40310451016040c1e0301d40512031400104042c900c00c881085d1030340c482d000c000851424129190b804071103032917102e0030343c2803600c041440f0303000d004081040c041903400f0304034a29508111440c001c107a02100d0203440100c1107428061074206229185c1750804e04800300d5055030012815185260351040648142e6803183c040b1260500c1095080d21030054410700c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 69896675 1250 69895425 69895451
    0x6050f18030a02120a05010c0503010f0902090d02090907050a09060305060609040f060c0c06200d020901020705031209090c0301080d031805012a0203090d0b070215040605040605060607111003 84
    0x1003c5102c4c0311100a0210400c80782045400d40700d44000d02000c00008000600400001c0b58180090b184900c0300142c0b200c400c00085070a101c19040040e5020030b80c2000c0011250b4000b504100781c55055032502c1d0070b1603032800da080070380e031031070100600e641c00190000b02e00f07042c038488440d03219029800c0305600300d460f0380310700084a40c003074400740000b00f0f0f446e00201440320030302a640860107000c0ca004884034104a200046002d41e86651070b12a400042d10b001f141c0c403c00080d0090100202500c559114805e00709803107601c040c42160180446200090b031030501441505d04036080b2001a05001002070b00440041c40b8031201450800c40c00d818210100d031003480341000c0036446503610700d841c2c46403407804080c1c040d10b00c03184000c40d401009105216100d9021070000345900403e0041e00e910b45a1043c0d04042c4032440d00e01180111100300018046a40c02160081d8080c610030401603c030311091118500c03420f60090a021100d100001903802c3c20b405480d4071a01c18600041c1c02042200c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 69897925 1250 69896675 69896689
    0x30504051905011d16030201030b0f21010c0903030f050304020d080c0105010302040b03073f050c0a0f060221040503010c1d1c120c060c05030a050106050f18030a02 72
    0x8010b40d45a9922402d6400001c01c1940420314149280002e01c401462240020005051404001d042544446000245440b010800e40c02018000e058450f44994a003a58203d006000350f40310b02507081c0190607900324017900c54001030b00d80540d00c0c1c0c2610313540000240c1c4d182c0e201501c00c07a0458031a00c950400f14406001400e16460803d00100382c4c0e51440c0100804d8907410051148240c000da001003200c6504010b41c5610441c40b11005c10260340400c0d210921141d109043c0b22010ba501c0503030008000004c00d4603014108200c0e0400110340d1200c0c00c0100002050141401503031060079040300140c20202103070088005a203a01d032510340c8620104c0e007520f150003121008201a010004400075690100465250701aa501c046081e078009010f040f442d0304880141440e80c01d444407000c6503100d1000d03e14210381000050081c400782d0a002401584100e80c9001694545400400d50364410002c4661401420f042c990034100105841c070300e2400d0391130103158944240c805101c0140c442d50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 69899175 1250 69897925 69897973
    0x315100e040b0a0903051207020a140601080c0108100905130309090c120b120f0a05011112041709060a0503010509090615060c01061203020a030f05090d0f020f09090102030106120b06030703050405 86
    0x5408ac000360f65651030144580c0c01c40000c218803d0700803100611003c0c000107040740c0e80c80300910346540580ca4100c0003842005854021100b002e0038101004545024205d0905400d4801c0e6128941c81756504101e00c11121400c14190004150318003421031031341d0980200040c900001c08a110043e000e0401902d011105006213090360491903030030b02440000e10416010408540e855440c000c032022070a90580c00041c40140404606d100000300106a2030640b108603001034100b0750340d00300c940400f9145400c02d11546101e039800b41d000550003d40810114010398040002d1400e03c6094010800075400100c0114040e642c0c842d400260b60f443c1c802108150380c065000307041c0301d81c1c15040041c5009041a041c06c148003040105503115207a450600074001e40068403000e03920007520000c2d518420310790341350f0b0b8807492038018000c5070301065006604850090700c03428500c0300b00340c0f861825125400c04040e07000c0b40c2400010380081c080d0300700d15401031044060380ca4541d0320288641c81c0002d09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 69900425 1250 69899175 69899177
    0x2060d1d0d0f1e08130501060b1801051804021c1a01030b030604030e2106071805010c08030c03061c06060608100b0a1d0315100e040b0a0903051207 65
    0x25440d0060324503001541c10701002e00900d4031240003c015007000c1c25006a81079800104889400015080d05464407074102d2198804001e121b15544d80c24001680c1d0070031459590000d0980344001a0780d070003502110000c460307900d070501c4044404010030000b5041034820044549200701c403601c61035068424604c01e0440c6450510f043c592020005044036410000c0e0350099000134280000301388c2000d000040c01c84101d54003040311043e6140b20f004180d22144203d254800c10080c05040c581020b400180c105402e008036120f00ea54100441d108440001d0290000d0b0080003c6844141864010b40c2d02040162661a880740d01e40c520100c031584400c004d0380d20960f580400c0c800103900024140e04420003e030300c11181c41c01c01102c480507120715141c2009000f907500d0054280049980810040d04000b42500c0a425020f6045c00c071114044034455420280140c0100e0325074010040e1030300031a08145081110b5481d29402c00042500100540a020040c0920b022a5040400e007030300c19121 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 69901675 1250 69900425 69900433
    0x60c06040b060a051503040f0204060303020f0607140a1d090106170601020105010312030209030106211707030203190203070b130b090a0510230c090a090b0d02060d1d 73
    0x100741440500024090b010034031490002d1010409a61010448000d805201018a50b03d03100c1e45008110300c004910003e400900700700002082c0341e000b04414210720303590700645269964900044541c1c004004031184514800d024000e0900d2152007845400115601d60404600d030300d00c0000c5502e002640101c0024110100650700c1c020b04208032500f202c82800280980c5d41583e484509614094044404055011030031004035542500260000d100d0120500040b04502c1900d6648a4441c44141c030108100390120306540345038012034070500d8140c4e01031420f11070218074501d0b03054007a6501c0401c41c8000d0140348081003840c4410b60240e91000500060702d06941b400064140d4004c04851580e0081c80c5861b020441c00300e40030140039044200000c00140c9904007030248404c90b070301d800030700030ba8a0030482020000740050034060005c9034103c404e103607504130880654284031941034000d84010325a100501300720003d000c0784907145c240410303400b4200e2114042480d40340c0030804103500c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 69902925 1250 69901675 69901681
    0x1a040e010b03010614070b060f04141501090509060a0303050c03040906081f05060a0b13030506040507061b03052a010f0f0f0603050316050c030f010902030d17070c11060c06 76
    0x1400c81c0703400741e0a01480b0701c802d0802840382c07a19480010002e101074055003058020300310a5030b46611a0004c2e000344d22111145080000c10101440c0d140c4cc000d902251910102060505d02921045e2198400074a6045170f2030441d601160242c01c464110325040c80701380400b19028019024036005804450f000300550404081401c7c5e02e200d9102400d20154540b4084c8075442d210111104291001c11721040e0391030a0b06200c045040905900140c66030003000140410010082440f5044540d0396a501c0d4240918100d8460b03000b03074131440100414003c00208100c0b4400300700b08404a5030000510500c0d841d25403400e801e54600a4911a1032641d94109040080d0a48030f4102c01071582d5004120840c2150740e19950382c4100380c0f452603040159405002001070402c18048000d2000e000e030b80d0b40040711160175020340302d1003004900c42e01440c00e040d01960301c10f410090381e400500d62029a1a00c41100c1602c0c800d00801040c2c0e123141740015400080d4903803100a0401481d140c0c0107082c585 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 69904175 1250 69902925 69902927
    0x8150603070905060f190b120a060e060102060708071803080706060803040501120b0a030602040b0409060905100504240b0909010803090907050d020405041104031202070303091a040e010b030106 85
    0x104203810542d8001c1c43c2c20103000d0740344c441c08501d450b1904269141d1021150408440401001d540d0141c001a600002c02083d59040e83d0841030241c280342400340545034441034a0880c00c0800c50b80240141e025100080c03240388115a0680c01c4217007802c01c5c0500c0c0d0040860040000503076003090304e42d141d0010342403041001d103200700001441701d040a54141810200001e006100d0301005079016030f2144040001340d59611020002150301101c1150703036a030358102c44a60ba40040c441c2c0c1d20340b14078140c000540c107003107401418400d00c0d0044580c404a07040c981000f0083c200c00485030a11a00880c00780d41040c0c0d2681070402a0043c02c001c20380760300035001040424034058000d03c00366007088c04a54001c1d110100b90580014081c00e1403521051900507940007406558000d507030060810340c10003580d0314404010710550380a54030b82c54901d070801d0b80c107a903100d10a00c00180042c0200e03000700400c072100400d03012840c05038068249400d5944030128009e00d000e8202c0d10500c500000100055 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 69905425 1250 69904175 69904183
    0xa020702030c010f200f010c030605030709020a090e090c030109140111130603020906160804030308060f030601030b130c15020705010207060203030619080102191d060403060f020408150603 83
    0x1011007482c01c0140c800d13892200416040750341481d0440d4141c40050217030110020300c01400ca01c20250300810242100d410000c025086a06c2041d009014480c000f0882d5078050084422103089900e0380d5030000d24190002c442010024403101c41343c01001c558031400c0c0d40038020061400d000d07080d40e580c9070285c0d04841c0e0840b10400c400211110040084021081103501d8810880d03402d4100140c03180d4000300070601d50704c200b4030115080f2803000f181d80c0801617000e024000340da000c0c5da200b04071a9a80d006200550806407180c070f500d603001e140108000b50343c495015510200d10001d40c0c0c1070301c800b5900c6412881d00ca4010385c903640d54800d0400c6203540c0c1040f02c040105801d00c001c1034003600c0d114001c2e4480c070000e46514003829a80d40c08081050000e43c50400901240d0000c640e80c000b0034070003040842d1481202c1d0700107a840b001417011607007251028103448000401c070f64501f038519902c41c402803648204000c1056020f101c002208601880010030900150140c0000b40c42e10344101810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 69906675 1250 69905425 69905443
    0x5040b04120f0c02040b12160303020d03050105130504060b0409080702150702101112030a0c0332041a07020601170610031407090516110607020d120b090a02070203 72
    0xc01880c00402c240055202608003280da0701510005000703036074040801c40b5100d0030301d4100d00341d2103052a090101e0580541100859001c0d030300f41c600c0b1801500c811020f80d0002e218040c0d0044503c203080501c08155400281c10178800c2e0800075200074a00301003401c0d559403e003780c808181c0400c000d015410406000c02541c08402503043c0380001c00e030700107403d600307450072201e0404c4002c5038044015501000803034110b20441d40b215480c2d25101c40940080c01c00c42c00c0000000381000100d0401039a0911106416081601e0400c60403000e000424800c4400901c2514603118403282c400d403040e142c1c22458052106030b4007601c0a50706001c90141c0851021312115403940c002c000300003142c11480088001d030303580301c8040082d82030700e400d49a160a240b500407110842c6000117010824a09041d17000011003680c454040340d0642c6814640c44110444030180543c100d0f08800304410b10480484030b00c2d0303805400005a051406011507402002140c1e0301241a41c001014070075440c0400c50050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 69907925 1250 69906675 69906677
    0x11e0c121512050c031f0c0905100e0303040b0a0305010519050a0302010f030f0c0206190203150603060a030606090506120a11040c0504030203060c03040b0702031e0a09030605040b0412 81
    0x80071a0090a1014448907100b002c0241d0b841200c800204101449002c0c04504010212031100c891a280411442c1c1c0c894a143c22040c034007440501c1460055804100300d0f0401001082100800c5101765000b281c054142c0b54540401c000100d01c0804890203403003d20650369001600398100703002c0c80800c01c582894603640b901d0302c280c2001123903141080d51003074950a00c0c100e020546484001d4002c0c0c09102805115142401d041821032940004c0841c0f00d84181040003002010310074215040344810b0703844e0804862802003030305290034820011504040b0160110076403e03035907120401281ca007600102466030b00d903400d101032440c1190141865207500c034007034501070889580d88040341014204c1c480c020350300e0308000e00d42c040c054801c2d00d0007107270041d040d80c3da01c0c503010f180c60b21a0f900840d801c803500a2800c002c24000c4bc4000140c804101000c40000388403580500034035020b400527071920081200d407442c0800000e029000c1e03075001d60700c200c41440a904140c40c10342d04130642006054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 69909175 1250 69907925 69907931
    0x60e01060518130209120604021e0d020d1e0602280507020114130b030103050114010815101502030306010212030603250b0c030d0605010309021809011e0c12 69
    0x80440d826049100c00300303004480303a028100f4462030160103030054800066100d58402e0562158220203d00c1c288a03a108545a40865052038100c02022144082d290303080780c03014589000600300410581c0381c60340207108140d0404d06955099400380c0c11030384c0881d0030507000f203036581d22031000403440390000641454500c558244d84000500c5c5008420010b41084010002c2480f480400c0d01244c1081c03012080c150341080e1503c0420295a101384001c442039803900307019000202d03c0c65016416250b0283c00b8081100780603070000e03003c50000d015519803800110300003510100318103111001d4021500607689030b20b8004006400e10a020300c10b5101c1c020204100000c1c0e65011441711400380080018407103032820501841c1c1c007002c640d0060072000c031001410054081000014041c404490107080c000302d0740b510011800e541c0f004900030340050512003074441d621400d843d407560050ba481d00000f00f400d2031614401c0c2c0417681d030707141040e01903640400c40300a541c080344102140c0ca000e8018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 69910425 1250 69909175 69909187
    0x506040e04060f090503160b010504050f04030c06020d05010e0f0a09030e0409050c06030403020106031e02030601050906011e050405040c030509030f070507030b0f0f01051008040b090106050a0306060e010605 91
    0x31040c4010000d000402640d51200590b41c034403415030000780829040001c480d01c450084819100f00d22035620306032070310107054000007800c0c40d04e030150318458581d840c43d13803549803101c0d42e00b40d07000c880c0b045c1c084a010b9000c2c89403100036112441014001c00740d400400040f400d10220b411544100a003007902454123000604001c80d03000520000641d000703582c00182110a81040750500080f5164140d000400000344014540d054000c0e90a40e0b005044075030303410414443c901c82c3c4040700341000750075030840b80041025103090f42c2170ba503000006041002c600c2c0400c00940040d20460303000780d004288040340910190a1510452071b05400906040101c5c2c14002341d459903d0003420f9201010b00c1c1e00007000c00c10000e092058200a40c0d0010820711a418841012000c1e01c0d000c07100495845000c80001a01d407900d0380c1181101c080c552100d500b10340703e94680000504004060456a40d04c551000605840d40000c0300c00035805404002a0b140c01c120005062803c183d1181c02000024411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 69911675 1250 69910425 69910439
    0x6030307020a1509090203040614060d050706031d06240f01080408070201110615011d010c111c08071101020a0201020303010b2b020711031209060d0f0504030207030b01050604 77
    0x102d50241c68001405000c040f8055208031a903d0300c0e508000c8009002006000811609403c4407800b003910980740440c1d561840309201400c03031a0a0090415800306104215a90095110008248581071b000304400004400d40c1e242c102c0c1070711281c562484a18841300e260030740026101103040120b81c001c85414429000a0810001400c0600880800543d8108580c0254182e801041014058072414035000100c03049038103014071140d0109031640c6820710245505001c090162038140c47c0c0f141d02e0400d648440383d404042c00c4481d50040c002c6803462b0018440d54001c558a00d12a0342c6d074656520940c0b5041a0080d0314044203410f551003070200c140141e0b000f00549065404000c001350319140c20749641c0311241140c01c3d0b82100d044d1a00014610100103800602e54180100c030b2001b00d5003220028103030b4580403001803504c483d03418800e81c00c440c80c0140c020441901d0707814022555004032801c8030101c1d03030191001c8002d039118400810800082030305503401080c2c11280141040d18011f6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 69912925 1250 69911675 69911689
    0x60714040603050c070203070e100501020604150207020312040f030c050916051c11030702061f12050106030614010503070609030b13032304170c031b0a09020315090603030702 77
    0x19207001d250f12440066218554281940c1565030003c044940242d80c4140b132945100f003c6d40c000c2c03500140c520700891154000100180965031090b0510110b51540154000035002510308991600502d800804075480400142016100800500400310b14616214204142641c45680070383c0340541080403050010094121040c8541403940c0daa0385484000d00e01e0111a0f0315003090a0700d8180c43e0b00b40c9a207124042c41c0314500507001ca40d45030300c4400030210149440c1e5000e00b00300080d002d003804000b40c00307010714003c5031142001140b1141c403580d4000966603003901c2d2400e00c0c035a89004005030b10301002000010503407030030302c0c1d01403a081d92100711100000820001400c101c20154800b058401e501e240d6002640d0f6803818170000c8011140610b42e03005100e008a290024114407000d060042032110444c44010002d0021141800344100c0300c00024015640c07090701960300046000082c00150721400c0300c0f81c01c1200f010509003c0000102020f44403034026482880000c0058596076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 69914175 1250 69912925 69912929
    0x21e060105010c1a04080712111c020102042102010e06070809150409020a02011407030e060a050408190302070302010c031103040b0c0c03161110090902090a0b07031106071404 77
    0x8a0701c1001c0c841242002240070403a0410704425044c00d4040000f8072401c5070150020728425003004000c8404071000b2500e4004a03026a0301035002405c04091021140c80a002c0f4200d4500004d03040070b5036264480c4000041000312495200c02c031245c1c00071503901c03203c2d00c5044002120000c2c200100760700c82d92958000c00c01003a024904820010301c419018009a4004004000065680706080304009000e0140e2000040b0f03a02c070000701050400e80240110340c0442e100000a001f5991142080310181070301030030542d2503000410030005800402d800322a03010b9129100035944030568a0000e0840e65008440d00403d803a14815040054201080700d8100c0d40081c425403250310341d80080c114600c01c4401041c02440b001038018095044d180350000941d0062281d00c50480c101000c0c042038454030140507000504070807060140400c5a80a0044210080c1146101a0300d501d685c54241e4092003040e008600c052000c4405850b040260700e921151618141001c1d508440480e00307a40214 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 69915425 1250 69914175 69914177
    0x100f0b0306100b03010611011d01021803030c0d03020f0d06120b22060207030e1c0c0b04031101050c0c0901091b02010b010509011d04020d1509020a0203030f0c090306010b0a021e06010501 82
    0x3d481040c901e03009d400c4007004900f0540400314929103074401e01d00030360048d01010700c031881038204800103203804020340e14481d503020003424515404000c11002548011040c102031071040c0034030752400ca030622651024001401203a00f508165040c0201d140000400110202e1041246820003e01d0380d080d0300700090384610090b89a9102e0301e425190f01c0341000105801007400013000740d90311071201c914680580524014042591a8072860074540704601000d0f00d6170403090a004d820354440c030000c00d4070200d80400c1d200d40b4407031080040c40e003580a0740000010381c5c80d0050f00b660b414604030340b608142c0150008006101c810301c00a0120b014038124203061004490300b2107a00c02d043c1c83c6c071032002c2c0c400a104659a0036040003200c001c0c20803c8442d0440541583c0c045020280d41c400c890345898260015811540c1d400800640c0e0351000701400c40c1900c0920240d0314644040044a010303100d25400e1548601030000000e10306074001511002c500401e00d0000e02c2081d0118070b1a06440c02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 69916675 1250 69915425 69915437
    0x30a08220f051c0806040b060903030702090612030307030c0807081003060e10051303020d0504060c060b010e0d0b01090b0f180705070c0e070e0a031e05100f0b0306100b030106 77
    0x15400e1060600300b107003d40004900810040041903680580c003a841004100c6041201c3c140c40400d01c0014060940c21603010ba008010f130b503001d45840d0381d071154000401000c044503050529460f9043d07400c00c0d640c03500401c0d210210240c05580000c485a4081c1840c504840a03241c42195030007941c4e200d203c045d0840f65a011600d010300814000080c0b40b036646841030025003045003007a00300348000401074006000e06402c0d000e1241c407030001c0340e04981440d9070320b030403415082d00e68200034a06919942d061002c40c820300d40080c0c440f1024000c05900039016a456980361010040c16107091030301d01485810707038107807a2070166210005607030105242000300e4034079030f074a04090300c1d94400d000340a4551051280c7c001340c0604c181403414411903141d501d00039808101700a1140c1c20800740002040a048120780455956444018030034440c069011682030b140a0b40c420301c200d0710302d40e94450300036440d074080c0740c10381c201004810381003c4903414003800e107464070300304500c00c1c04107005003410044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 69917925 1250 69916675 69916703
    0x80706090615080703170306150f0910080402090106030506010c0f060603020a08100c0f0903020607152316020c120a0827041e0c050706020309030a0822 67
    0x6034040b000d160241c5480e01a20b54498032903a5840c1110301c0202d600c0c908120201c180f00d045007064a00842000d0244189218050110f00712900101203201907810207000603041c0741d8511003110700e80107080e1030717940381e038180b0340140310310250140c005105240c141424030485903406990031000c1c1e50003003074841c03000c40d10345004805000d280e840079501400520020880c12000b040b2143c005441e031004000352038880c0e00c240d4180c28074109580129095100030405030601070002d181c4240315407904c0b032100748000550000c80e16490307900214200000c0809800130703603000c0004d401c1650b20307030185038864070f03004002c0d690050108a50700a000d110440c0451100c200022420660b1080149031a8907030201d6015485000c03024030401c82a8414078030801d403c1600c1100813600900301c0c40c610b0000c501314400f000d403040c240150b0400c00d042000700c01283c000d202031405a08020b003d0b507500c491841000b00101e201501481c02580010b01c09030b20304402d4489251700035400140d0340100c039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 69919175 1250 69917925 69917933
    0x10c29090c010201090b13140601090507080f010605120415050103060213080a0c0b0c031b060708010e0f0a020a020f0313081509100902040207080711090703060f051e0a03050607030609020708070609 87
    0x40c42342451201c03a4407079100040303108041034104a206601540da1201c455891080c844420402803144001198003008441555003807400300c2c80c3d00074042c01045180c90101c0c09044102c440907801601e0300c40c4d0105030b101c50140300c0096500181140b10090241e41190313110f041000d8030034851504070140003e4104525039041c019296449100240707034580c0d042c1030758000e440f031200310341140c0014840c1c0000b103001039000762198000c02900e4070801c05a40c07a80c000f400294452000325003548104c10700c18007140300820007001019502c00100c062030f458411014070344112019609840fa24480801a00d0080040e4034040d100810b407000c0303840600d50020400138400d040010301440000903604090040c5c01c0d12040750f01c0c4003a40c824180b45e407035001c22000c90701d41d0700607124003071202c09081080303162030300c4c503520407010300c1d0098003280a1741c2002900da010303164411516038215000300000c0d283c062245400500100030b09502e8030500d40d50701034051041c00c00080055944a4150b8240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 69920425 1250 69919175 69919193
    0x7050a0909261c0606050307030902011e02100f091a04020604051806030607083c0f0f0702030403020a0e04030c08040b0705010e0a0c0302010c29090c010201090b13 72
    0x44a00c49000400000045001120b40c030000c0c00000c83d030303c58100ea090403486845800704035003032581d41e1402d60b11220000c4001d095840400e904000e070395000801d803045010381d220312045076600140550402c07052031070262000300c9031540c2400e1600102e0000324100c644455925642c08203082c110381d54074070000d0f80364040c0b5040180c004008080861841e2410505c00380a00811000c4416554030a00221070100e01251505a4205514034042e04c13000301449012400c180750016020007900c59142910202c422620f86001d018200180701c0d1500401649542091492000d540740500b9500031882c201c50b14810741e10481928400201031500c64008001c0381a0301c03012a95640e969502c5082031600014019140c6501e400144030b0b00c0390000590325086c50f80260203034071541c656001034400320601c0c40705903803140500c0c110303101d81c402e500c0314218020000e241d402a14140000e07901d203422503880d081415603141009000104030304e00c1d41d550384950106804110411140350403502c1e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 69921675 1250 69920425 69920453
    0x70201060801050c0a020c0d0206090d020a031b05210706050307121104050307090626100204031a09030a0206010b2d030117190201120207020d0b060103060807050a0909 74
    0x50b5468681400701181003031004100304002c039402c94a2412401d010880410510368000358803150030000e408481c185512104070b40b0b400100080c1e095039803900e43d1030407000c584107680000d904100090007249082000079020344400d5410501942d450031085a6031005030045505002c00400040c0c00284218181081d905011809201c0c1c0d88566140c170205400900031144a070007090b00100f480384030f41c03050600b11140468240e00308902102802950b40c0411b0802e03034540295141d0f0114402c10b4001000114420210681446d40d5201a030001d95005008140c56800422049020690000308203040d15502e01c1810b0307640250701824181c28010b4040c0c000d001e082410850144c0900d030f0050350407581044002031500f45000900d03a142d1000c10900904c03241c4003906035000d5407007403000c9604130104c1c1c0401444e003486d40c3c00160742d40801c0c08040b030b000000402000301d19641802614000d2a1103070043c0241ca05240c001440340342e00c0d0041b0210540d07078080010a100c203800d09114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 69922925 1250 69921675 69921689
    0x30403210908120403080a0c050d15210201030513081209031b0106050a060c030503040b1b0711030f06070207060809030d11031f0e010519080d0e090f010803070201050307020106 78
    0x5542c3c03411030348411031250704a8054000c501e51200149490009015681d0414001c1d507501d0304e02010010890002e100b4044202c044004401010810050f80c105150038001841c3c40d2001e248640d100040565a004000900e40c43c2c2c941d0204001400300170613202e0100140310340c0507040c0d48030402c8903c0d5000307040132030305807012244590818000662000b801d45000f601c101c00750302e445c0c013425110040711070801070006204000181c00b140d0540750a9401034520f5060011080c540203d0380102d411056080c0e402500e035a0310114546003c00030003070405840806040b5501d081c0101a485496510035941804007600008050b8602402140c0b0301c0d00c01d25100b0000c1d9080841c4070741154004443c0c81e26508103200082428040d007d80d0502100c40301403800c080b0340c0c203180030310405070455083342d054440c030410041448141401160100d010580c0d45401d405002c4d800c100c400d1401410103d106800900144041c07407021080369401c41d02800e0503513507921440800c0f401421a684110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 69924175 1250 69922925 69922927
    0x51503061201110315090f060d0b0a0b0d030905100e0306011502030906070606060807020616030207030215010b0310050415030f020a0e0f01060311090108150103140a020717030403210908 82
    0x8039401d490408480320172800c0c0d8030f030003040e41d40e1881e0950321201500c0c29507004031440100d90014480e0321103140d0010000501244240c903250110320071840b40c201c11004240c13440d1061050781000004444800803134900010201c1c8620040b988a00042c0289200bc0b00c2d400702520400b4003c100703d55030130401401c101d40c0d4103007500b450710003060a40075982c00180c281012403084c500c00035056014040c41d0581e02d80c55034407014183c0096008060407000e50044110803c5001c00850003a03000f8004000d45559902c0e2410007401c2d0035695070840c500c11443c0120018a0900c01c0d098401a282d1140766400103686500004584101035800342e40b410100c42b08000e0014030300d400013812103d641c0c40500107400200e910002c6401803800ca80e00103000d040004850455142d0000c220070010b0400107255040c02452043c51141190a084c0382900000d045003004240052130f0f941c05800b0a6103811410a40d4000f0b0921010481c06400314000e80c000e03554050749a841058010380c00701080d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 69925425 1250 69924175 69924181
    0x10201060b070b06030613050712020112230601030207030203040302041a10032c192a030507080d020d0305090102040504050f0a0b090712021305120a0501060515030612011103 77
    0xa40701165080300d40c64083c0c0201c1000c06d081d040c110707a9002502343e0107030241c940d49042862002c804044010143d040050b400d43c1c88160514a00c900380e2100e10001043d05055052607580780712f031030054421410148100703e5540425408400d4900f502e604172400b03c0c82d212015071211290110764819544001612540c5000e2505580008824102880058009450741602c1d802280c40f02500a02e50f40040101d181c916224410300008107201d0f061380c80f840c008125000d000810310f100340102462910310b09109002e01000054010303c41c2c4002441d8050860b04000d40b27440400c50054181030b151008502006000c0d01036902074180503008111504e0301300612681a04140c0d00040c510386040e5161019040200385207206031265201d1091180b80b8413070b03810013075110b070110480000d421080441c0c1d60f510007030000d030007035480802080c0c002d059092682c21115503501892145904a05800e442605101030f03950115049581300034400c010a040e0f0f000d080d04162114500c0b07400010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 69926675 1250 69925425 69925433
    0xb09070b0a361508010506030103150b010309051b010801120c06050c030c010f060303030f0b0906120316110901060e0a03080a03090b072105040503070206031b0d06090b010f1d010201060b07 83
    0xa952a0003220780e07104c0005980e2181070000030703c0b0a0001810b0700d82454101281200150882a0219410b240008451855440713035070410307281400c6020b00040b0055450501c0da130202d1698094112500c81c0c008004541c1d4403a160b100d514407980c3c050003c0803406051011080c810341e441e440c0203400070300c90601c5040c1011300809081c00211702103850664007010b00f4a40340304400018401070f000e01c0240d1603440070064a00003048070902140310410001003240750704000703440c12511611440c42c00013403050400c0344541050700404200310400b40140115a50101642c0483e504100b495a46522284085010704100d040c0680710400340c2041c003a10541c0081c07103503610780764000407141086110310b0410554030261401340c201d0b8414414103000d480c0c94402190410b070306040640d030f0419142d40c0e0a405800008404100c9651444200301c07001c05030084000882d42442e01310754142c851325000c0e0404c1402c03541201111925010541c5590003513000c039000e4144a41101d4a4074102c1c90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 69927925 1250 69926675 69926699
    0x1202060408070b0a030c02010c020d030f0b13090b0c1204080304140303070e0a05060a120b041d0604050c0108090d0309060e1906060b031e040203030d05040b09070b0a36 74
    0x14401303002030f1425015002903441032180c2c03450640258081c20448620f450210041c205018461007129921010384d80b02e84c0e18042c41c01d0803e0720740c800102ea0880743c2d00f031245000400800c4950341d4141000750300c01c49889005140c1d4080c2c2d020525640703984860030010300e822180b966210705032000006010340325800090006e2240c0b000c8803207640c02521241440843d0196007140b401090070044001183da61a40101407290b1003d080044d201e103040c0c1081c0456003409941450320b0b00140240030a120302030040750601c0d842070a000350141851507103107035101901000c9038105507540741c09108206494000315400840c80c0c0450703141c40d008030521209010001000c0b10145d280400004d907514080042e03034030036516286959510740000c1d9007020150710007401280c0c50f01040200707200c00c401c0f91140078020741c058150b40c40f503450080ea60b10701d410141d4109480e09c030f10501c00d8440459004803101a100c1c2140030305460480b1804001d0041c4044c07140840515000d61400304003036400034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 69929175 1250 69927925 69927937
    0x20f0c06040b0106090807050405090c09040b0f13080a08090c040c0f03051005010203041a040503010606050c0c01020606090c0c151602060703050c09090702030d06030c17010b03071202060408070b 86
    0xc0d07821002d039982d00405d0703c50802c14492110b403608110000c02c6075250a90000d0381c07014580c01680d01011003240010404042154216940d41000c0c2c10f0080d26964041501e0340b080b00d80340e210300641c0d141d840301204e50103072a00c50b10030044214001901e82c141401200d401c12401f800a01082d140104045c04075402079941800203803414000441c9c242d002100038080300c0c010b0300514982400c101059520300c08055224001a00402c4002090b031400d104000040c030040d0b8400740c94072203501c8854108400403400504541c44001070000f143d883d1685a40c102c000340b0360305a503503201e40b040581846091420540305059a004004054928aa01c8050b150203503083e560b070345d900d00c0026001c039001a64404413469081c84411038900b0146113150300100d40740101d0b810024442002c1e001d4614a40040b25202084082040f11405105140c07280d0700c03040300240300d4210f0103004250b60303c440d803080d08058000c1c81421825920b031001201c010b40320502c1941e40a5450b842021503641c406 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 69930425 1250 69929175 69929183
    0x10e03090102190b04081b060a0b0109050409030e2202070501090b010611070504090c080d0903060b0618150702060c03030f01050a03030c03081b13080705010305010803071401020f0c0604 82
    0x112044800c03a40744030b440001507403140240c0a285c0321030300c07401c489030010030120b80803d2002c189081301796030802c443c0d8401d003c408008150410b2810004010010b5a8051401035040c455020006a04000c0714201c00e6001d54451882a0385441040024602078094a0500b03100080036005d000d4103400a02c030b007a0207001582c0351070340c4e200030486a101303401e4400900c42d00003007070512040c0b600740c100241d801d005418000e01caa0303e03004454180341d0780280c0e40c0b0105d0441d620402c100207850181c0480324104803130090074146801c0240c8900d00c00740315000d2003002308103600c0710980c0c41301040d0b45206070081d00103900c419608440c1170b62075100340c61440d102801c0380000a0070349800b01004084c0c80c0e05640d6045100442c6c1c0e401e4680c0c4101800d00e00c4406003a8008104500c2c0d003502400280350300b0042881170703621b8481c15506080319a084681094105401070201c25400012149001c0d4080210207444080c0c400b100d0081c01805460303458407400240e0b01046a00000741540502d0103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 69931675 1250 69930425 69930433
    0x1061805011e0303020607030c0c0209010b0706060b04050a091509090803100806061309030918060e100b0708030c1c06141917030712110609010c1706040b03010e03090102 75
    0x80c401e07405061002c00e00c00100160310000024001038420380103401001d01e181400c424845141d80018081e2109030401511120042200814030049028040051039014100c0307282074100004100d400041d4043c110f41d0b161200125a1001c2c0b04100300740041110030000c000c890554039040300d407036209943d001080c0382080c80100b641c013004181d0034098503004200c403050344240f0400342c0260944a01c25407e0101101c400110101100018030301c880440b400004d4441c10400c4500d5403540c0a021064280000d64041c04101208011101034641082d90780d9200d940c0c24030a84010711510042c03a0300d0440c103000c1350500d08900e400c5001a6250249001e118988030428000200c00e0340c100007056501000f810013803c00241c3c007040107900b104007503e1070410790381c4841d80322041d075030030210000b03820310540120746000740130442e04a00244024800c07148240d4008003c0340f0321000e0340741c1095111007c100940d45552108039501c0c809070003803021401003c10191290080e1a1f01405806 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 69932925 1250 69931675 69931709
    0x120c0c02010f1103031306020903010e010509160e13051207060219021b060d14181603170a121508100b090f0405010b060414210613050106180501 64
    0x2000c0c500260b41c49200000540c11030b541c54041b41254603400006580b51642000400031a440038001c003800c00c1c0988001103954144480364038a400d10f80c9403d100000007148040c84850400c0c584075401c18070040000c3c10b400c81a041c001e0900d840b00420540320180040c040003040016005801510850b07000d003c2105040c1c801030f610340382a40341c081d0403111559141d0240b8500b9030050301005006180000d0941c440310260704d200802a102403040d07604110794282c041d0300070410f2100c04180b0710398140a19285540e404040b594020b00803ca140e804601e15038031a02c120781e16001e03800341c1c46090252480c0f020506210724081d01540c120b600580c44034a07078600c8280249680300320090400c012550f1013030700804035000003410858265488030000c500c0e5a840c08060300c0900405881074031008004070801c58403605100c03924100140c83c1560b000c030350202180c8a6408010340150801105440c41c2940c014040344e003188140740c08219a03420085440d40c410340c165404480050300b07002d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 69934175 1250 69932925 69932927
    0x1505060705070503390d03110f07030804230310020703020c090403050711030303010b0405090a09061e050714070201030504050a150e01050c040b03071b0609080903010c110c0f01120c0c02010f 84
    0x10314039190150085a480e586c840003a100e0a0b505118a004a058846554501c02d8003030030410250300c1a1010100410140a0103440085400281052642804040c202400400d4440c25016000708d68168045008410302d802448800384061004004000c2840c103403030050a6900302480940700c5504080051420f402d000040b2416958484805802e00e480d0100704140c07100c0c000c00013000662a0714400b00000d60740c1c000d544048000542500c800c000c0240410211500105600100f00140d04216001410340b002c03030300369a8081c030300400c03546e0b103c0c18101d28201c00941c1c01480c0320708205000980c00382c2548911041301c1c00000070301164844c0d518060050007a40296101400304102003910f1500036501041248034400010b061400d0540b0b0b0402243d0304d00009840b92a00010190350528080c42000702840b1941041c2d00e90320414845a40d0301d00c40d00d04c07000d00812240301e035845640e00480b8040540f00c01c010050141c031a26070f034020003e003806082207002c40c50a1440707195072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 69935425 1250 69934175 69934273
    0x906040e07180b031308040e010807031401021201090b01053c030108150601020f0f060105090601110606040518010515030607050f0d02070c12050703020111011505060705070503 78
    0x480300440411300356280d8200740f09506412000c00c0354801e204100000305071042101c098021311440c005001407a19500b0800111074076407101501e16441004911088a0204400b50641d00c031008009013801001005036080c0c031442600c0050217000202045000500011008034424035009042e030182000e091205c83e03000c03c0c00740c09000c0d00041034004003204070110983d80a2070510441c0c0d00c01c00c4112420b41048042040da00036604101e005001c1ca040412080d90094003e1070300e01d14202d81000105c1d00e60703901404840c8a02d40780c4c0301003440300000e180c400208000c244001c000f81d0600e0707005c44d090708010915103070186c02243d002800c50b900440035210700d0034040c4645440c203074080c030301078000b54059041201d15426440010525040401c121600d192180300280603050860002401c0c0001445074994168104410181c22507904220034048400070390340780d51201c0c002d18080d420b007401c41e0812a01072150303000a094003403d06240c0c000c5c6003d660303803030307400e0407106a2000c2c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 69936675 1250 69935425 69935429
    0x190e0c0f0603130c0306060f05090115180b0c03030a05150108010608090312091006230904020f10120b0303030609010b0d0e010203010909060608061e0405030906040e0718 75
    0x21054101a603a003040c102a4000c580c84807840c14401d609240fa0743d240c2004640c0c540013620203e54803541406001c071075050321005800d0440d89113031150325003822141c54842440504d81009840725820300c403003141c151000b01500a01410b29107074079801c10203a0f5a5007007180e19521382414800441d0030021840e082081c0d2800603500c09815030700f09502965001c0026048010a100030094403082145548000f4040d10710400500404111400800e0984407241c1100c102d60a08803404ca0f03400d091b500c0c0001d80b002d421382d907001c62580d603800020800f641e1400c02a030800c040c8214010810f9001020803c00a00004100f160a44000c01d1541d24041240c0450300204c41900500c020300c40c9901420b81446180c00210342407241d05050380c00da07002a440351346160b49900a11b010000c07a4061007010b41040b034018405858064a95082740701001d01c80e123103010302d000208041c003c0500c00c0b580340c2a0f0142079103941c0c80d52207503c80a040011200c000004018000001c003a61860300b140003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 69937925 1250 69936675 69936679
    0x2090c130312090b0a08010509250e03030408070e10120f020d06180303050118020708090108101208070212010216060222080d17070801030609061103190e0c 69
    0x642155200401c0d1407144440900f400800c04000440c20040d10041c910215150b41d0341646c0d515103402d0010250020b44140b500940842d0040034900f1001d120340b4221810789041854050814082070852140f40c0240350940550b04000c2024100b15981d5401200720400702d03180141d40d01090740c20416016401003d4400d049102e80151404900d011650f034091080016000c000803002c00348424000790850111381c480f00100607203091204140409222244158a007642c5603441d040d2610845203d1814080b101c03020800608406d4a480d0107003541c0c451005415500b820921099041548100d02c204010507540e40115418001d90b14800031301c1c185080700304d41030b45d1903002a401100d060045a9854000c1c0b10038104185441c2d00284204000703000c40920500b80101605c901c00102c050700440001840015503000c141c090441b130f00b241c0c0c0080d0182c22880c0031701c0508000c01d001d038412140801031040840c03090803503480f40c2502c1756003005000e42c09030b0859110b0540d075000325 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 69939175 1250 69937925 69937957
    0x3090e15040203041109040f0605070c030c061508060a05010f0b0403080d090201030b0a1d0c090901030b09010912020d021e030a030216080406180801060f030f050c0a060c02090c 78
    0x20440782042d801075500a44203a07a0020100b040e13101281c1031101c12a016a904502c1640000c20b03c1228482c0b1504620545841c0d40352800e0382c0ca010f040c2c0d04280030001c01c00307541e8020a00c01054280d24120240041400340c514070304200c240300019040a014040b010054a0700007d070f504248001c0b50112503021341da00b82040320f4400348100420440c070301a81415151b0912000d16a070b0b888568020b050f443d11900c070510541c154000c1100802841c00540040c1008002e034543d0b83e1140850440c1d41c01300390302c40c89580d40346403180541510754000740001c44440b1210031440c2c010030030501c4132200340e0850301607101158135041030000340c0f03c2104058004101d044081c3c0d20a0b0001c04100c03000108481282c040f036543c1806a0348594441d03c00598440b03441650100200000030081031518001d00c010342c1011080768511856120007408100254001c004014007032105c2030489400401d0400f00980e900740141606518440c124414515400001d500000c030b0015120a055000400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 69940425 1250 69939175 69939211
    0x706080106050309121902100612120311041502060601020601060e131506051e0304050c01050d1b0513060302030c03041103070b0a050904050105060703021c0e0901030f03090e 77
    0xd468580c0090034203210760196402c030002c0070b85d007403008051382402100a000031200c0f490f0b0090030011150b503407001090900200700043d041203200d0b6118280c00c20b400c0003450f01008070550083c04421404101e02c17101090010745920710484074181c0042503000e88009603501c5004a0b1101001d0040d08003045584d1008801410700c1010761400c0507084900150400d044404100b040e41a40d01c96000200c0000d00c070544d03000d10050244440011501d50b07030540c180740d602c10b6224848603105504222011890580b604140d8010410b5000c0c044000c011402451100501580c40a00c4801d5806008032000861714443c1c421240320f07410503198542035032140e030b0342c0300c2c141080080b00740c5e49489280e00c042404600c030300c0203201014040d01c44941d959500d0062100790f80e0160700c0b05100c0c020601c00100429000320310605406840c110310244903990300001c2d5810380c030300ca04031600016080008000c000e070f280d410106503030081e00d80b003203000e66a01c80464000011142e507044c40100c1604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 69941675 1250 69940425 69940427
    0x1080609010e09070308130504270807030c0204021201060807020d091820040801060501112d03040602010b03061003020a060c0302070902070323210c0702030a050307050d020706080106 81
    0x2103d8000300c505041d14149662030700c904201ea00305d901c03088200324080108000c94989807240c04000365003d544e094448603207450740e862000545a01908a0000007503000030141314403891200164014011512a032407031074081e2006009000705008640c00e02c01055030b080c000103e40a10300784ca50b5070050401c0c100140210744242c0040a0001180c403614015560428840c44541c03442043c15120b4869140610302820341e09641e0203035060040c0d03180301d48114400030608440c0020029001039000d04a03180070100702c858146948a81d010200b80441d6256041d00728000d180c40440444847d9250820f84645140c078910009521030124a000c00c5501d0183c6200c046141c042c0c0107a4008590f1500c80405a0340403201c11000101e0524001c1307030042e0400441007620123109503007030502000d907c0c4142030708052890301e03a44407150310008941d140070f542203070138076940902a01c80101c5180b0b0025500d0300940c1040380c81d402900d010180481c80020004112902a51500000c3c1d2800754 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 69942925 1250 69941675 69941699
    0x1104111c060e19020d1104080d0210020a0f0309140f0a0c090606050a080717041101080702010c051b030712030e07060305070806090405150903030106030b0316050114070c0906030b060108060901 85
    0x7030b0745c81c011500c03016420801c03807100010340010424940942002500117000a0401d0050020301c0441407041c42408092584450802400000350500244809140c10f14075095a01c02650900a215201c500d40e448280460050380e0940f00f034010240c0d4a40791400c42e000e03600140502c0e00040c0e030600c03804a4a602c903510f5690000d0850400030b07410344161a44480801080b20280d4100d02090f080580035644541c01030b0f48102c49100070059803c180100030403d10408007401200d01e207003410f00600300414030898600c80e07407007120ba628030484000060f0144c60003c0700a0041d00621400040741806401003a00c500410b980e41c1c400c075620b406c10000711400c044d00c2078940340b03c0c901d00f5110410400907901d000700031500080d80c4961421100034142c070010100d80d40240c2021b51803110321845203041c9415034809081002d540c1e50915403000c6103000b5440f018142182c1c042c000108002154040d1090700d010303035100c0e40c05907a0038006403840d8006503225038215140c0001040174102c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 69944175 1250 69942925 69942937
    0x40201050307050d0603050a1202011a060c030f0c06010501031104030c06050f040b07030804021201090201051603050c06070509041808072003010c051b0604050304031104111c060e1902 81
    0x100300f2a0a01c10001d034000100c4e80190005c54450b0b000b40400020712541600c2e180c8410300502c02400b10030010f14011540d4651000080c2c0910300c007003000e12140d6018400e42d110b40c046c8161075601c0c0c880300309000e60742e00c0c5d0a120f03480c00310b46081c00e54107a03100c0e010700700c8080d00d41101d070006142e440d002c0c0071525944491264850441c05001c045071250b581c0c4000c1180d60700a40d240c01450034240100078903520030800b19140b90785009000030050342c2007006e0342c130785901441d9800440d032807509058546100e401d4ac6032001d801401c04000c07009403c0409899407a006031000c2003e8420365006414031080190064141c0c903060008400090748034081d4001c4150240d1080c1092021101107425151070484ca44040360010504032020300341c02040003d03051050004045500701500c91035100d2060340000707400d030782e1054040443c03a11160010b4030100004000c144d500ca0041510344541c4524602c140c007224200940000c07420422448140540c500b42110340c0040040035020000794481 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 69945425 1250 69944175 69944177
    0x280b0f010207081e0307060603150e071a031003050607120e060705070219050310091106030403170702010b0901030311060f0105010e101202070b040c150807030b0d050109030f030b1206040201050307 87
    0x1000000d0005031f007070140078015032041031030386140f4440c00444000d82c0d0341c00c0d90003a2903030b001c88410080800e1801e19000040c40004a281d5030b81c84408038005c0e02c000c0c5400103001c40c8562414000143c2c2d10400c4010040c07225081003125003940710409407642c000382c074103100149062000401500c1e100c2e50480308000700490480d0384669500c042810500d4070201e00d421942e84031585814004014003800501c0e000300e504d14990329250f03034050710300301098030b15151201c088000910b009000354444055540024840c4006613943d10b001440307200310f465424018055100400d80c850050308800b4140c6805854020f445100f020610180321880d16900040040c030076419091a140c51006081381030040c04900344a1800307003030442441c80350781c3c807a0101c806401c1c070107890780368040c0c4000d0b00901545404140c01281d0400260000c581c0b01001d062035203060034241c101130b0451000901c1201035201480f081c0fa85004201e8040340e0000c00070055048100054010340c410f5000b1a4000c80f1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 69946675 1250 69945425 69945427
    0xf0504050906120f15061e1c020a0e04080918060a06050f040504090503070204051605030402040504030e03030c010507030b03030412060e01021309050906010b160b280b0f010207081e03 81
    0x5881d007450310440c10000805c0305a1402071240c41d040901c00c40c03141d52031001e00e0407082891a0007290b4403450b40c036414020360182803034802c21591743d0000710300200240104001d032410942041665a4401e14002d44924040c203031400031060010081d40c031030140101030200d1103141403c03e0b03030309611440e03500003007000802020405139540e10480f4141030180008544039041407041c0000c460010708541c00703c0000c0442030440343c2d0301404680e84541e041d80d020401d52940c0c501594a007880c0c060441c1d05000c00f00b000e40721800c0544c030240c442d2040d5030303052150144000616890748528022030501462076005800401c5140d005070200d01c030030000051030481b48913a03c80e201c00d120380021020549550902103030510810010b8090030004521501e0422500b0000040c9081418010500c4070007400240186d05a4121004044903141401d49600c1113900a0341c0200602d40259204801d9400440d1035948005448000d4650160040240e6010301c41e284900100714407040405101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 69947925 1250 69946675 69946693
    0xa1a0f040b030106080c0a080106080706180f0308180402030c0d150f060206010e010b04060f03150b030a06030201081302010203090d0f05010906020309190305160f020a0f060f050405090612 83
    0x609204c1d650040294402422409405200b003003950b2070583d1040140e81e05001e02407100c01e00204280044440070b0030454105a070b00e1440301c201350015400704140d0910014004148419074000304094410350003441220440401080f049000c2612281080720051002004d540000d40c042100c03900d41a18901c011a40c80207141700012007604124016000903004000c018003c07440b85005d0414a540740b400c0c00e0070000c00500c0a010900c2e582c0c00c164071400c104404c400036114503405452100c5a01e03075a031410104200c042e143d00c0c0b0049001505260014000d09003151000c842d40764164091032404a52204120046801c0c90040c1e940e9100d5500043c00500709110303085401e0711400001da102e1800f0f07440c00703062402084500c5088141128070304d00081c0d1002c1220707146402540d5030744040340c0509041600768000e5200070f4101280300c2010400e00d81c3c04c1541d41c1200c1c0c2590340c9013403202141d9003c95103402144207881e08100c0f0103000c241107140c405901e4103000780c588121510a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 69949175 1250 69947925 69947929
    0x9230a030602030a230c0a051c060603061503060f0e0603070806040f0605070e012102040f09050406060605040b070206030414060a06030215040305071403011107030203120a1a0f040b 80
    0xf0b4010366484444540c0c07814002c0c07070711001400c03000c5480010030408807a49410f40c0390b04d0481c0300d4040c07210100080000c43c0f04402c2d051250600540d06140000c100403911514090020601c1d03014203800400a442826245840790003038100f928117001101d448686418016190fa54028081c42e904d40600320340030071f1580040016602c180d0088a1156146c1c240e81030010440314090304e880100304c02d6007141d011a98102c10600c10706e601708840d000460742c401d21403000a00039500010480d400551000640145c0c83d00024021400345000b000411f0b55030000f519144a14820100020b1051080901528144d0040c50784980070f8007540c110110440400c1d401d0100c121000640b09660740c0303040c015424581030445800c40d2500c003591900d41180c43d5151380300201c1c80707100c06819a40d080c1c10303110344080d0043c85401c46110015522010a407130f000c0e407207401400c00b0060444404000941d103001c94090101d003140c2000c02900d030b6100b04828428182c54003820550859214401071583d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 69950425 1250 69949175 69949177
    0xa0218010509070f08040f051204030f110901050a030f03050702090a0f0e010203060303041a040509160206060607020d03080703060f1d0f3d06091509230a030602 71
    0x114168840055103606010070880821400742c031210820101500f0b2000d80781c0c0000040790401e4002440c00d070b0b130401601c0d00a1500c00016888450950003141c00001c00c4841c48a019800b0302c0340603010300c1080c4540c02d010b40746000f442455071086440c1020004242284001d24650740285441440c150a580100d501c4001c05e60f0740107542e43d640d5044044d6108284122000300c01d107803000b5403031030800c0e81c0025500e01541c010301e0400b80c003c0c05802400d04e200021100200400391100c103c0c1e1610f04400c124484000341c0030310160040900007103007441c04000305c494061703000341050000425602c0844030424000c02c44424903581c1d000c0072401640000561005003030f0110790400100c80c08080251005000d8550b80701b810140052100c00d086101090801c13200108210020340f034207010807170040440700c0508e00b00504620002c1003159102c0394400135180300c490300c00003803448402c04590741e42642c8201a2801d007064404034022610310b24000e1040700040840d0760851701c0323840c2c035422 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 69951675 1250 69950425 69950449
    0xc0301020a0521010f0b0a21060602120301060203040611030d0e030a0e01030b0306070305060d200109080a0b07050d020f0f0a0e030f2d010c0206091c140c0a02 70
    0x1041003c00d20700703205801000d0001c040d0300009a50002949407170392202440c00c8070b000d0403a0840b4040f52840c4d42a1003511680d54885240100e450100c0b0700381c140f00c00030450341c0200c0005000b1708020045004404040b03904890255000f949031074540301c400c45502402c3d0804403c50f0004002c02100501907001d80d001d80200d10020f555101502036020300006840408141814200038200f902540e0214690758080e10605012030031fa030300c020000b40c1d10507002c0c07002000340c0520416441c20400100903916402d0080c2c07150301d41c06488242e0740b0b5a4900c1c95000800700301e544000614641d10a201801c1c07502901d803005410b042490000310303425040044944041070b8049100741456070f10a1903401c25020541c003510b20103810b041820744130fa02c603007018a45e2608001c1c503c02d0300303a5801c070900b1440aa40e0300070440ea1003107480080d01c5900a55080507a031007815a022485901d40c800007a50301616110340303206e41043c0c0e144c0070241e0801c03520b1b00c0b528000c03401d009016850b41c000d1292 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 69952925 1250 69951675 69951677
    0x1180314011a0f0d15020f0d020a0201140c03150619050d0f1e0203060d02060706090b060108070e09062701090e0601120803150301020406050c010b031b0904050c0301020a 75
    0x1000320280480410500e10440c0c0144280070492800701140c0743c4d0854480b5041c2c010b0960003c40000c400c24502920880c10b0828150400250300391815429a014040d00312440c3d00034840014a20480c08500e030741601e541c6110507040012070310f0b40c0c80c0d001d4a1009030b10041c10301800e150345460020103641c0b03164940030206000084640c6085102d00c0784210591160f8010048a5030406001500d800013980c0804080d60000100f1190780e07900500481c89540240065036503c0c43e4500740025051002c0304550031080070022a01075030190030f0640c400c0b50741c2da56189007824000c1c00c01174950009031955402c010a5414a401c0160042003070001ca84039401d10700301c42d45031140b200c0c101c41a440004c1d00342e8203c1030051108a0481150586440d080954161a502c0d101030b07402c09941c0f01d00365a030380b5610000e40011643e800c00090450f11003a80000c2000c03210f0b84050644800e0104c40c81514210041810459440d007000102e801a0042c411a9040c03100e420200b0300320b80c00b80e42800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 69954175 1250 69952925 69952931
    0x503180f090a021e0d140c0c0a120c0f030e100c120c21020f1e071202040b03060106080106181d070203040906081507110d1101020702130209040506090408090118031401 74
    0x19044000300307112075402802980001c0d2404802c3d0410395110b03002d8040052032b200c190450001010700c101ea9003000c0381e80050a612120f940c134a0040c1c000e080350a82c441c0500140803044c44014040d6429203c901e070803007206400003030348401c110f5800e0003104007120300390b003004842d9440901c50140c5500103e92a0000e01205048040440c0780000600309000545d503020040e10910102144003402c5510300c40c85951605103510024026080b4201d103030350184a0f0030b00004500754014041412100c913034a602c1d07810306401c001580c031801e8602900d00b5001c165450400a0003c0740043e95102d5210700c10303241015100c84000d000d0f5400d6070f0154219502106900141d0481585244e4020340c10b81880c0203130320305c1c070000c1c0c0b501c0d5403014100340309003c07488160208141081d01210f404c1503006210101002c01801c5420094000c0100d0a0150389060001029030400c081b081c0d01450b002502c1c01c0c100200f6100444105220104d044140b4004207400000290a640028040c000120003c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 69955425 1250 69954175 69954191
    0x706020405010905030a050a02041d0604030f08090111030f10030503070b010302010f0c110f03070f08010e010b03120409020d091a1f06050d0f060f030503180f090a021e0d 75
    0x1003110200313400182c800e03000040c5820000d079000401104903076041d03c02040004003110070313600840440f51050001d006060030402015800007103003c01c15117503100d00110f5143c80040a00b00c400c4811741d140089001c202140980c4440200c850b40a41d00c20400141c05450795591401c54100d4402110754076602c0005000715070b005484200684407615060054445a072201c4100500f151601405500c995038107005648040c00340030043c000442c012580b0703035620426507000f4034070452400740390b5207040b001824a02e00454698a01d202140c0d404d4201820448040b0003075011403000802150342e00c0125001508915120410141d40300b5105918500441c6021302a102c4894440e041a4007200510140750008296021f000c03581c0c000003106500304502038000d04064108000d024204000081008000001414000031469208440404040601541f2181441c070140e00400400018000c82b84640c09042e812403641c000c1060b034403400c00000c0340c41d4400f01480384616151658 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 69956675 1250 69955425 69955427
    0x24080c0a02031b010b1f091a0405010c03020f250e090309100c0210050703080604050f0c0a0504080a1b060201060602030301090902190e0a0605061602040510151709030306010909051b070602040501 86
    0x911001850080240009448c504021144502c2107000321814003803880841024180708106292200d080981280c260303103c140d448a03662034000b000a1020074078548040b0707044504071070050140b1000001035060015560410403200d40c042160801c00c40250f00700009a51a03114501c0c0c040d1103170311141d070348058a05005128502c001c01c0303d8010b80c00e15007803215020480f003401e07602106248146460b2134500708110b031180f00e2548021064810511101d082c4809400d10050085071030b2f10211206903500416800d0700c100c6d124980168000b0300c010001000d01c0e400c420301252005104145458030000c01d20b580d41519082100e22401078001c11484080b1841200083d02089910340d05101c0b10950a509607200b420002b400f07035880f44082040d05012034001c0c0e015280344800704148804007030340142544681060100c0004d03070240416078010000c070860b801a030060b0341302c142c03080c2002e644001400c0013501440d074103c0d200701d40305000c101246c05024154810400981d49624100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 69957925 1250 69956675 69956687
    0x106080c0c0d1d100c0b0a140907140118030f0204110a0f230708090406030b0a0203040c0905040807021e03030705030702040f2c0724080c0a02031b010b1f 68
    0x415002d104106500c40070b040e003001c161182d055000c55070b85140e680701400c0d00060500310020442902304942805040303503004c62000240c548440c81348210501720301c01114080024402c0d515042026103040c0003080ca205075103080b0500251003c0740051200b040d402e2680e00140013000010072108101e40455800b021548406880107100d0016100400030000588103008000740140342c00281e41a568a480d00000001c507044400c2414628003c422a406580215001c40d22842e841d940400d0070390051041034001c0d5040321105081500036428407248643e00782042200e00203160f130501c025601080203007001485000616110045481848203540f0f213040412280c40c03e02d040ca050b106004007911038155622480344100d4204550344504040b0b254000500f040020342d072003100c00c4996500c01410f01c0aa586486c00d580c0e8400d010b08884c003800c044440140c000b0000d04155400d0f4180c41080110890000038181ca450000950a0b0b0302303c0c06a001e0588032070800d1409070350482 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 69959175 1250 69957925 69957977
    0x3030b150414030c010f05040e06040b040c36090c02010b09100806010f060806100513030807020315040819090f032a0303050f03190f0f060812030106080c0c0d 70
    0x20a246c0581840b100c8054141c7c001c5004141c1d141b5504d40001d4515642c60700544450040940304000e4030b0018000104000d03030f003d00e0310202070380c1d02c140d8081c40c0d40314480040f80c8014070152540080d06242181c805016811002400c564a880d42c1002c5595241d421034040e9128988900382c10345402921414580140c0c01014030906d520802c0007e590071445666100200701d030b00512941d5920801c0e6428001e0940300c954041007113402101b04030903030000f07000d0140214112031610131b5101440552035000c035402010050148415450100b9250300442c411101d410b00d888120740303552454030202d8543c0d20a84d8070344202c0242420700fa4204040550300724246007080a150b023140c401078030318460a034000c5001c020000000c3c6504514040d03818061007411014401d680c1201c270400c0c00750103c210f407514898640000043c54040005144407a10442c4180d41d0071a0728041054501e514020456080520b04006003000ca9405009039843c0c40c8140d141c0c50141c0e42c0012071018190204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 69960425 1250 69959175 69959177
    0x20c01020309030c120f01020d02090a0b09030a02040e0a05010509030a03050108060906160909020a090602010605041505090705040503030a050a08010501050a080f0603160602010504050105061c03030b150414030c01 94
    0x10401e0381c41d10744004c1a001d21040c801d40702404000548045c141c42c004c030711711544520703510102da424070040b03044e0000e128084044034000303000c0707840d4000781155100e039008095055104034000c27001414145c0254150360002c20541d0442c00071525a2825110112034880e4103810018000e115250184611030240c20450014405840c140c035681c1e586990140c022601c03100308101c0c1ea1003d40c8148001c42c00303891100015511b50689041c080e02c1c3c07100c2401008095400c1220100300c60a040c0b28a0146690620304014014507000a0041030340000d0802001c010f0101f001003001c1c1c41c100010311240c4455542e6650319101058001d22561040e00014104903041021900c05944828126042030505035025032035111807002920f403007003201e8000b00070b190082d40002da01d0380643c060391090b8003a20081c4510b0b900c5400300401d0b407900004641e41d61400c800400d010030301c643c2c0841b078220310250444030300030010f40f804181504254401c116056958450706441c0c102070051240151007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 69961675 1250 69960425 69960427
    0xc160602030f0a0e030318033114030c0f15040e010e160c030509040b121510050a0e07032d0b0d0201020c190b030a020310060207030209060d1a0f0106020c010203 71
    0x34403413001e850f44006050305900c050816803d500fa4a405d100321103210000000c802e0085803030b80241c10b07045203080b075101100040e11a000940042460030030441c0d8500501400b0703001d0601c0304000702e002d0b4180303155400c0000d01c03071a2054916880002c0010b04065884809950b01d440801e0030a81c800070074001701383c050740c14000300160708403076024149030785410041c2c0c03909540c0001c9002400c0349001907a0050103c3c80c9c0955604001c20031288020782074081000c0703503075000507500d107101841c0715041d004060248100020030108902e29041407a600d000b1442c1016282240491662010111308400d881000d49100080f1031244402e90002500c60205244c11500041d4982c04502e60300c50180c3c40c0da070490741c20465084d0303464000c0c1942c0086213449061590f03990000f5081140d140c82d113100c1131440411300c01d00005404080340e0340101104002c2d078890052102c0c10320103410480b4502046e4580b00d042c00503034013807a0702c12203110344000c515602d400402440d0003102440d960642d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 69962925 1250 69961675 69961691
    0x302090102060703050402030c15090418020310090507091a040614010903080a0512040c06180b2703100b010206070c050a0b0705090904030804150606080a050c160602030f0a 76
    0x1802054840c3d104259050000301e03580c1d607001003801c08009294665104059211900c07a0f422502c010703200100c01501c042240c1d0640d440b9113a840c080d8120041c1d456402030340841d02103c110f400001403644200e09694407075682d040058241d914480f068490044560b030501702d14107042c400da10040016030100c1044605410003e0120740c00c9000141929900040748030016000700116510081c050701001003504c0c02741088050900c243c06040001103010945070101c500e254211400e90341203081403482c16105006400c4181040c00800c0000d079007103080c1040941d410701c84444500316a8102141460101e0f0009003400350040002d014004414040404110000390807501c1c541e02025050458541c40c1c01a502d500410401e150300c00c140c03e041204051740710501c03600841c80348111401040240032440180d80c018000c8200141107040001c1a0020760b802076030700f101c600c82c0344600e09070040c4921800c48014000c183c2c2e0440d00001030101c0c41c8040c080e180c0e400714a21000b00325000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 69964031 1106 69962925 69962927
    0x150405010507050a1b0f1403030703111c021e041d0108011107110a05040c0314130f020112020f0301090b040f0e19031403010602160603020901 63
    0x150800c0d0101d503410340520150386144c0c810741c40780c90785000003500c9151844401c980544529407100304213004103503d060181094000c0c0f4014544d00d143c24440070f0240c0300d01540001003042c08209107442c1c00b113500d13541c50368400b26820243e600c100490f00d080b02514041e11082078034800280014820400c1e920a0054804030262081240c5c0e0b10716405003291903200700c00c0c10b0b078030f0b040000500103424520320480c008002418103511a8491001c80c1c125482e80120348040f9030f81d21140c20500400904250b80100310041e410004951a5112981010070100c000e052003403044205040c9586078068445012303a6000107030f201d40c0e403140139401800f402d01c2401e00642c50090001d0420080b800342d50780300b00300b0300d0061484404814422214a50180c026020040e440c52280d040440340e0300154000d0403264001d106100540110340144045075028030141803042084500503 = true := by decide +kernel

theorem cover : BRFrame.Cov 69784175 69964031 := by
  have h0 := BRFrame.cov_init 69784175
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69784175 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 69784175 ≤ n) (h2 : n < 69964031) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
