-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:57.653253+00:00
-- url     : https://prove2.me/submissions/d3abd4b1-b223-457a-96fe-ca902b037da2

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
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) : PowerSeries.coeff 1 (lgF K p) = 1 := by
  have h1 : (1 : ℕ) ≠ p ^ 2 := by nlinarith
  rw [lgF, PowerSeries.coeff_mk]
  simp [Finset.sum_range_succ, h1]
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
