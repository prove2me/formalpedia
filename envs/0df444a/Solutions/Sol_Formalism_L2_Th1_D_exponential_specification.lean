-- Prove2me | solution 1 for Formalism.L2.Th1.D.exponential_specification
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:35:24.780104+00:00
-- url     : https://prove2.me/submissions/a6a17b69-56ab-4ed4-a80e-e49dbe871937

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_expF_eq
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_inj
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
open FormalExponential
namespace Formalism.L2.Th1.D
theorem _root_.solution : ExpSpec := by
  intro K _ l hl
  have h0 := constantCoeff_lgF (K := K) l hl
  have hc : PowerSeries.constantCoeff (expF K l) = 0 := by
    rw [expF_eq l hl]
    exact PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have h1 : PowerSeries.subst (expF K l) (lgF K l) = (PowerSeries.X : PowerSeries K) := by
    rw [expF_eq l hl]
    exact PowerSeries.subst_substInvOfIsUnit_right _ h0 _
  refine ⟨hc, h1, ?_, ?_⟩
  · rw [expF_eq l hl]
    exact PowerSeries.subst_substInvOfIsUnit_left _ h0 _
  · intro ex hex h
    exact inj l hl ex _ hex hc (h.trans h1.symm)
end Formalism.L2.Th1.D
