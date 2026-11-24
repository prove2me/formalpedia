-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.law_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:09.175056+00:00
-- url     : https://prove2.me/submissions/6046669d-714b-4f5c-bab6-be2bea99a149

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_cob_eq_zero_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj

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
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) (F F' : MvPowerSeries (Fin 2) K)
    (h0 : MvPowerSeries.constantCoeff F = 0) (h0' : MvPowerSeries.constantCoeff F' = 0)
    (h : cob F (lgF K p) = 0) (h' : cob F' (lgF K p) = 0) : F = F' :=
  lgF_subst_inj p hp F F' h0 h0'
    (by rw [(cob_eq_zero_iff F _).mp h, (cob_eq_zero_iff F' _).mp h'])
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
