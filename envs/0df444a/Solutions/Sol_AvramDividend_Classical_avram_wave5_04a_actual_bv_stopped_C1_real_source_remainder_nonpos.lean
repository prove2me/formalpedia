-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_C1_real_source_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:16:41.520661+00:00
-- url     : https://prove2.me/submissions/d0132341-3d84-4132-a11f-c068612b102b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Real finite source-jump and downward remainder partition identity for the
actual stopped controlled BV process; increasing C1 derivatives yield a
nonpositive signed remainder contribution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
      (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
      (hgrad : ∀ i : Fin n,
        0 ≤ deriv w (riskProcess X x D (u i) ω)),
      ∃ r : Fin n → ℝ,
        (∀ i : Fin n, 0 ≤ r i) ∧
        (∀ i : Fin n,
          (∑' (v : ℝ≥0),
            if u i < v ∧ v ≤ u (i + 1) then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal + r i =
          (((u (i + 1) : ℝ≥0) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
            (((u i : ℝ≥0) : ℝ) * X.drift - X.X (u i) ω)) ∧
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) * r i) ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder X hBV]
    with ω hω
  intro τ u hu n hstop hgrad
  classical
  have hex (i : Fin n) : ∃ r : ℝ, 0 ≤ r ∧
      (∑' (v : ℝ≥0),
        if u i < v ∧ v ≤ u (i + 1) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal + r =
      (((u (i + 1) : ℝ≥0) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
        (((u i : ℝ≥0) : ℝ) * X.drift - X.X (u i) ω) := by
    exact hω (u i) (u (i + 1)) (hu (Nat.le_succ _))
  choose r hr_nonneg hr_balance using hex
  refine ⟨r, hr_nonneg, hr_balance, ?_⟩
  apply Finset.sum_nonpos
  intro i hi
  have hnonneg :
      0 ≤ deriv w (riskProcess X x D (u i) ω) * r i :=
    mul_nonneg (hgrad i) (hr_nonneg i)
  nlinarith only [hnonneg]
