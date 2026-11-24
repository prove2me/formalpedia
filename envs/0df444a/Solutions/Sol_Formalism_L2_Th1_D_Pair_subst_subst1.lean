-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst_subst1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:03.111914+00:00
-- url     : https://prove2.me/submissions/65ba58f4-d156-4550-90c4-49a7fe534991

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  first
  | exact subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb f
  | exact subst_comp_subst_apply ha hb f
  | exact subst_comp_subst_apply (hasSubst_of_constantCoeff_nilpotent fun _ => ha) hb f
end Formalism.L2.Th1.D.Pair
