-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst_single_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:25.018393+00:00
-- url     : https://prove2.me/submissions/b2059fc9-68a4-4630-bbd1-02ffde8b5640

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1

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
    (x : ι) (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_subst1 hb (PowerSeries.HasSubst.of_constantCoeff_zero (a := (X x : MvPowerSeries ι K)) (by simp)) f,
    subst_X hb]
end Formalism.L2.Th1.D.Pair
