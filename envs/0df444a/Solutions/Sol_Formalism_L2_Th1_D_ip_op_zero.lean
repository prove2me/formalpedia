-- Prove2me | solution 1 for Formalism.L2.Th1.D.ip_op_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:18.767823+00:00
-- url     : https://prove2.me/submissions/e3db2b17-bffe-400b-ac31-9bbf27a03a00

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
theorem _root_.solution (l : ℕ) (σ : K →+* K) :
    MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (0 : MvPowerSeries τ K)) = 0 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hq : l ^ 2 ≠ 0 := by positivity
    rw [frobVar_eq_expand hq, map_zero, map_zero, mul_zero]
end Formalism.L2.Th1.D
