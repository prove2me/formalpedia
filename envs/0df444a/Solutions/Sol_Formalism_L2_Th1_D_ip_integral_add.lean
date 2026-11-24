-- Prove2me | solution 1 for Formalism.L2.Th1.D.ip_integral_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:14.703252+00:00
-- url     : https://prove2.me/submissions/85cebdfa-cbfb-463d-8d5d-dc1d79d990ae

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
variable {K : Type} [NormedField K] {τ : Type}
namespace Formalism.L2.Th1.D
theorem _root_.solution [IsUltrametricDist K] {f g : MvPowerSeries τ K} (hf : Integral f)
    (hg : Integral g) : Integral (f + g) := fun n => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))
end Formalism.L2.Th1.D
