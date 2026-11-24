-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.cob_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:16.77802+00:00
-- url     : https://prove2.me/submissions/7dce7b1e-1852-4ab2-a873-c7466fd46169

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

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
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  unfold cob at1
  rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    PowerSeries.subst_add (PowerSeries.HasSubst.X 0), PowerSeries.subst_add (PowerSeries.HasSubst.X 1)]
  ring
end Formalism.InvariantFactorPaths.G7.LemTwo
