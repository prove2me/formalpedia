-- Prove2me | solution 1 for Formalism.L2.Th1.D.ip_map_lgF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:15.526661+00:00
-- url     : https://prove2.me/submissions/63893781-41c1-48ed-981e-b514033b91e5

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
namespace Formalism.L2.Th1.D
theorem _root_.solution {K : Type} [Field K] (l : ℕ) (φ : K →+* K) :
    MvPowerSeries.map φ (lgF K l : MvPowerSeries Unit K) = lgF K l := by
  change PowerSeries.map φ (lgF K l) = lgF K l
  ext n
  rw [PowerSeries.coeff_map]
  unfold lgF
  rw [PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [map_inv₀, map_pow, map_natCast]
  · rw [map_zero]
end Formalism.L2.Th1.D
