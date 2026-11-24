-- Prove2me | solution 1 for Formalism.L2.Th1.D.FormalExponential.at_variable_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:13.153448+00:00
-- url     : https://prove2.me/submissions/bde8a339-7379-4111-a906-685c2fb1cdd6

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
theorem _root_.solution {ι : Type} (x : ι) (ζ : K) :
    at1 x (PowerSeries.C ζ * PowerSeries.X) =
      MvPowerSeries.C ζ * (MvPowerSeries.X x : MvPowerSeries ι K) := by
  unfold at1
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X x), PowerSeries.subst_C,
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)]
end Formalism.L2.Th1.D.FormalExponential
