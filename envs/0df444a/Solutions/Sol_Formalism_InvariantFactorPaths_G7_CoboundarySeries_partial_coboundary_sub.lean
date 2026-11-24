-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:12.194799+00:00
-- url     : https://prove2.me/submissions/a2f1abd8-b669-4ab6-bd68-a74795a79e2f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_coboundary_first
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_last_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (H H' : MvPowerSeries (Fin 2) K) : d1 F (H - H') = d1 F H - d1 F H' := by
  unfold d1
  rw [MvPowerSeries.subst_sub (has_subst_coboundary_first hF), MvPowerSeries.subst_sub (has_subst_last_pair 0), MvPowerSeries.subst_sub (has_subst_last_pair 1)]
  abel
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
