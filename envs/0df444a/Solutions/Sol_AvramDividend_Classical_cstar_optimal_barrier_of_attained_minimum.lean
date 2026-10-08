-- Prove2me | solution 1 for AvramDividend.Classical.cstar_optimal_barrier_of_attained_minimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:59:02.81172+00:00
-- url     : https://prove2.me/submissions/5ab91db7-6d55-4a1e-88a6-ee3acd144330

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf
import Theorems.Thm_AvramDividend_Classical_cstar_barrier_compare_of_attained_positive_minimal

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hattain : (cstar W).toReal ∈ cstarSet W)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hdiff : DifferentiableOn ℝ W
      (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧
      ∀ x b : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ b →
        barrierValue W b x ≤ vcstar W x := by
  have hbound :
      ((deriv W (cstar W).toReal : ℝ) : EReal) ≤
        derivZeroPlus W :=
    deriv_global_lower_le_right_liminf
      W (deriv W (cstar W).toReal) hattain.2
  have hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal := by
    by_cases htop : scaleDeriv W 0 = ⊤
    · exact Or.inl htop
    · right
      right
      have hle :
          ((deriv W (cstar W).toReal : ℝ) : EReal) ≤ scaleDeriv W 0 := by
        simpa [scaleDeriv] using hbound
      have hnotbot :
          ((deriv W (cstar W).toReal : ℝ) : EReal) ≠ ⊥ := by
        simp
      have hreal := EReal.toReal_le_toReal hle hnotbot htop
      simpa using hreal
  have hcontW : ContinuousOn W (Set.Icc 0 (cstar W).toReal) :=
    hW.2.2.1.mono (by
      intro x hx
      exact hx.1)
  exact cstar_barrier_compare_of_attained_positive_minimal
    W hW.2.1 hattain hpositive hboundary hcontW hdiff
