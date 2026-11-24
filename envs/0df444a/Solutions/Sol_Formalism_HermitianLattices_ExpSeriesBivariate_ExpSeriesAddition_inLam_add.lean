-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.inLam_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:24:59.128923+00:00
-- url     : https://prove2.me/submissions/59f8cf62-3aaf-4a86-b179-40f4b8c32713

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_expS_add

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
theorem _root_.solution [IsUltrametricDist K] [Algebra ℚ K] {f g : MvPowerSeries σ K} (hf : InLam f)
    (hg : InLam g) : InLam (f + g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  rw [expS_add f g hf.1 hg.1]
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro p _
  rw [norm_mul]
  exact (mul_le_mul (hf.2 p.1) (hg.2 p.2) (norm_nonneg _) zero_le_one).trans (by norm_num)
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
