-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:33.133718+00:00
-- url     : https://prove2.me/submissions/d678576e-1ac8-4c77-a43c-767c5a9a59e9

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
theorem _root_.solution {ι κ α : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) (s : Finset α)
    (f : α → MvPowerSeries ι K) : subst φ (∑ r ∈ s, f r) = ∑ r ∈ s, subst φ (f r) := by
  first
  | exact MvPowerSeries.subst_sum hφ s f
  | (rw [← coe_substAlgHom hφ]; exact map_sum _ f s)
  | exact map_sum (substAlgHom hφ) f s
end Formalism.L2.Th1.D.Pair
