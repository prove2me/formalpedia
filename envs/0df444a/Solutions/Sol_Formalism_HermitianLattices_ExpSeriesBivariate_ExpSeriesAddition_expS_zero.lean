-- Prove2me | solution 1 for Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition.expS_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:36.443619+00:00
-- url     : https://prove2.me/submissions/0da376d1-7055-4bbd-b084-d63292a03fe1

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
theorem _root_.solution : expS (0 : MvPowerSeries σ K) = 1 := by
  unfold expS
  have ha : PowerSeries.HasSubst (0 : MvPowerSeries σ K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  ext e
  rw [PowerSeries.coeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [zero_pow hd]
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
