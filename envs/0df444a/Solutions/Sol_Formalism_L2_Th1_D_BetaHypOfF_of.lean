-- Prove2me | solution 1 for Formalism.L2.Th1.D.BetaHypOfF_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:41.748194+00:00
-- url     : https://prove2.me/submissions/950ef773-926a-457d-a53d-49eb096f57c1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_isMul_root
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_at_variable_C_mul_X
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_norm_eq_one_of_pow
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
theorem _root_.solution : TeichSigma → BetaHypOfF := by
  intro hT K _ _ _ l σ hU F be0 hF1 hF2
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  refine ⟨hF1.1, hF1.2.1, hF1.2.2, ?_⟩
  intro ζ hζ
  have hN0 : l ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl 2
    omega
  have nζ : ‖ζ‖ = 1 := norm_eq_one_of_pow hN0 hζ
  have hσ : σ ζ = ζ ^ l := hT K l 2 σ hU (by norm_num) ζ hζ
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσ, map_pow, hσ, ← pow_mul, ← sq]
    have : l ^ 2 = (l ^ 2 - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have h := hF2 ζ nζ.le hσσ (PowerSeries.C ζ * PowerSeries.X)
    (PowerSeries.C (ζ ^ l) * PowerSeries.X) (isMul_root hl hζ) (by rw [hσ]; exact isMul_root hl hζl)
  rw [at_variable_C_mul_X, at_variable_C_mul_X] at h
  exact h
end Formalism.L2.Th1.D
