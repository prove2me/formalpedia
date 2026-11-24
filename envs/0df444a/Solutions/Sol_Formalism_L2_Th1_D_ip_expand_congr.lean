-- Prove2me | solution 1 for Formalism.L2.Th1.D.ip_expand_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:13.09759+00:00
-- url     : https://prove2.me/submissions/83da7925-22ac-4383-8c9d-c538ce93dc67

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
theorem _root_.solution {K τ : Type} [Field K] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b)
    (f : MvPowerSeries τ K) : MvPowerSeries.expand a ha f = MvPowerSeries.expand b hb f := by
  subst h
  rfl
end Formalism.L2.Th1.D
