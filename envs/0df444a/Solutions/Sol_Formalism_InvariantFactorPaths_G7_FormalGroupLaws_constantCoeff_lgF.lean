-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:57.928164+00:00
-- url     : https://prove2.me/submissions/f65a92e8-a228-464d-95a8-f0736ec46bea

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne

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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) : PowerSeries.constantCoeff (lgF K p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
