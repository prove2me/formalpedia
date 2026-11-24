-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.inLam_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:24:59.256806+00:00
-- url     : https://prove2.me/submissions/909fb087-c986-4342-964d-1cc6cd20bd81

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_expS_add
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_expS_zero
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_constantCoeff_expS
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_integral_of_mul_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExpSeriesBivariate Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
variable {σ K : Type} [NormedField K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
theorem _root_.solution [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f) :
    InLam (-f) := by
  refine ⟨by simp [hf.1], ?_⟩
  have h1 : expS f * expS (-f) = 1 := by
    rw [← expS_add f (-f) hf.1 (by simp [hf.1])]
    first
    | rw [add_neg_cancel, expS_zero]
    | rw [add_right_neg, expS_zero]
    | simp [expS_zero]
  exact integral_of_mul_eq_one h1 (constantCoeff_expS f hf.1) hf.2
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
