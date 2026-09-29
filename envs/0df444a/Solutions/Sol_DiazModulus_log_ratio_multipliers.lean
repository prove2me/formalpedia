-- Prove2me | solution 1 for DiazModulus.log_ratio_multipliers
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:25:00.212287+00:00
-- url     : https://prove2.me/submissions/2ed14ab9-9393-4a23-bc12-0e9a9ea67129

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_six_exponentials

open ComplexConjugate

namespace LogRatio

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

theorem exp_rat_mul_alg (q : ℚ) {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp ((q : ℂ) * w)) := by
  refine IsAlgebraic.of_pow (n := q.den) q.pos ?_
  have hden : ((q.den : ℕ) : ℂ) * (q : ℂ) = ((q.num : ℤ) : ℂ) := by
    rw [Rat.cast_def]; field_simp
  rw [← Complex.exp_nat_mul, ← mul_assoc, hden, Complex.exp_int_mul]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg q.num
  · rw [hm, zpow_natCast]; exact hw.pow m
  · rw [hm, zpow_neg, zpow_natCast]; exact (hw.pow m).inv

end LogRatio

open LogRatio in
/-- Six exponentials at `x = (1, u/v)`, `y = (v, ū, w)`: the six products are `v, ū, w, u,
c·v̄, uw/v`, all logarithms of algebraic numbers. -/
theorem solution (u v w : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hev : IsAlgebraic ℚ (Complex.exp v))
    (hew : IsAlgebraic ℚ (Complex.exp w))
    (c : ℚ) (hc : u * conj u = (c : ℂ) * (v * conj v))
    (hvu : ∀ q : ℚ, v ≠ (q : ℂ) * u) (hvu' : ∀ q : ℚ, v ≠ (q : ℂ) * conj u)
    (hm : IsAlgebraic ℚ (Complex.exp (u * w / v))) :
    ∃ a b : ℚ, w = (a : ℂ) * v + (b : ℂ) * conj u := by
  by_contra hw
  simp only [not_exists] at hw
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu
  have e10 : u / v * v = u := by field_simp
  have e11 : u / v * conj u = (c : ℂ) * conj v := by
    field_simp; linear_combination hc
  have e12 : u / v * w = u * w / v := by ring
  -- `x = (1, u/v)` is `ℚ`-independent: `u/v ∉ ℚ`
  have hx : LinearIndependent ℚ ![(1 : ℂ), u / v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Rat.smul_def, mul_one] at hst
    -- clear the denominator: `s v + t u = 0`
    have h1 : (s : ℂ) * v + (t : ℂ) * u = 0 := by
      have e : (t : ℂ) * (u / v) * v = (t : ℂ) * u := by field_simp
      linear_combination v * hst - e
    by_cases hs : s = 0
    · subst hs
      simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero] at h1
      rcases h1 with h | h
      · exact ⟨rfl, by exact_mod_cast h⟩
      · exact absurd h hu
    · exfalso
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
      refine hvu (-t / s) ?_
      push_cast
      field_simp
      linear_combination h1
  -- `y = (v, ū, w)` is `ℚ`-independent
  have hy : LinearIndependent ℚ ![v, conj u, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def] at hg
    have h2 : g 2 = 0 := by
      by_contra h2
      have h2C : (g 2 : ℂ) ≠ 0 := by exact_mod_cast h2
      refine hw (-(g 0) / g 2) (-(g 1) / g 2) ?_
      push_cast
      field_simp
      linear_combination hg
    have h0 : g 0 = 0 := by
      by_contra h0
      have h0C : (g 0 : ℂ) ≠ 0 := by exact_mod_cast h0
      refine hvu' (-(g 1) / g 0) ?_
      rw [h2] at hg
      push_cast at hg ⊢
      field_simp
      linear_combination hg
    have h1 : g 1 = 0 := by
      rw [h0, h2] at hg
      simp only [Rat.cast_zero, zero_mul, zero_add, add_zero, mul_eq_zero] at hg
      rcases hg with h | h
      · exact_mod_cast h
      · exact absurd h hcu
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hall : ∀ i j, IsAlgebraic ℚ (Complex.exp (![(1 : ℂ), u / v] i * ![v, conj u, w] j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change IsAlgebraic ℚ (Complex.exp (1 * v)); rw [one_mul]; exact hev
    · change IsAlgebraic ℚ (Complex.exp (1 * conj u)); rw [one_mul]; exact exp_conj_alg heu
    · change IsAlgebraic ℚ (Complex.exp (1 * w)); rw [one_mul]; exact hew
    · change IsAlgebraic ℚ (Complex.exp (u / v * v)); rw [e10]; exact heu
    · change IsAlgebraic ℚ (Complex.exp (u / v * conj u)); rw [e11]
      exact exp_rat_mul_alg c (exp_conj_alg hev)
    · change IsAlgebraic ℚ (Complex.exp (u / v * w)); rw [e12]; exact hm
  obtain ⟨i, j, hij⟩ := DiazModulus.six_exponentials _ _ hx hy
  exact hij (hall i j)

#print axioms solution
