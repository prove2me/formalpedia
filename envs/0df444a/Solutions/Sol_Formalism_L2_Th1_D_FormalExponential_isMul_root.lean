-- Prove2me | solution 1 for Formalism.L2.Th1.D.FormalExponential.isMul_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:14.52258+00:00
-- url     : https://prove2.me/submissions/0ba557d0-60a9-4453-ad50-314e4abb22f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)
open Formalism.L2.Th1.D.FormalExponential
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.FormalExponential
theorem _root_.solution {ζ : K} {l : ℕ} (hl : 2 ≤ l) (hζ : ζ ^ (l ^ 2 - 1) = 1) :
    IsMul l ζ (PowerSeries.C ζ * PowerSeries.X) := by
  refine ⟨by simp, ?_⟩
  rw [← rescale_lgF hζ hl, PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]
end Formalism.L2.Th1.D.FormalExponential
