-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.constantCoeff_expS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:46.81881+00:00
-- url     : https://prove2.me/submissions/8677bb01-92b6-416a-a0ea-6984eb27b526

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries

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
variable {σ K : Type} [Field K] [Algebra ℚ K]
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
theorem _root_.solution (f : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (expS f) = 1 := by
  unfold expS
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hf, zero_pow hd]
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
