-- Prove2me | solution 1 for Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.inS_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:24:47.566039+00:00
-- url     : https://prove2.me/submissions/8330c225-0125-4ede-9d3c-a410bfa1dbd8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
import Theorems.Thm_Formalism_L2_Th1_D_SubstitutionCoefficientLemmas_left_eq
import Theorems.Thm_Formalism_L2_Th1_D_SubstitutionCoefficientLemmas_right_eq
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_at_variable_C_mul_X
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_isMul_root
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_norm_eq_one_of_pow
import Theorems.Thm_Formalism_L2_Th1_D_teichSigma


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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
open Pair InverseCommuting
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable {l : ℕ} {σ : K →+* K} {F be0 : MvPowerSeries (Fin 2) K}
namespace Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
theorem _root_.solution (hU : UnrOK K l σ) (hB : BetaHyp l F be0) {ζ : K} (hζ : ζ ^ (l ^ 2 - 1) = 1) :
    InS l σ be0 ζ := by
  have hl : 2 ≤ l := hU.1.two_le
  have hN0 : l ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl 2
    omega
  have hσ : σ ζ = ζ ^ l := teichSigma K l 2 σ hU (by norm_num) ζ hζ
  have hζl : (ζ ^ l) ^ (l ^ 2 - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine ⟨(FormalExponential.norm_eq_one_of_pow hN0 hζ).le, ?_, ?_⟩
  · rw [hσ, map_pow, hσ, ← pow_mul, ← sq]
    have : l ^ 2 = (l ^ 2 - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  · rw [hσ, left_eq hl (FormalExponential.isMul_root hl hζ), right_eq hl (FormalExponential.isMul_root hl hζl),
      FormalExponential.at_variable_C_mul_X, FormalExponential.at_variable_C_mul_X]
    exact hB.2.2.2 ζ hζ
end Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
