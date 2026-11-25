-- Prove2me | solution 1 for Formalism.L2.Th1.D.BrC.phNorm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:45.017835+00:00
-- url     : https://prove2.me/submissions/09d6fd48-8dae-498e-ad78-0ac7ccc74ba2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
import Theorems.Thm_Formalism_L2_Th1_C_simeq_iff_congruence


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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.D.BrC
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable [CharZero K]
namespace Formalism.L2.Th1.D.BrC
theorem _root_.solution {l : ℕ} {σ : K →+* K} (ph : PowerSeries K) (α : K) :
    C.PhNormAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) ↔ NormRel l σ ph α := by
  unfold C.PhNormAt NormRel
  rw [Formalism.L2.Th1.C.simeq_iff_congruence K Unit, PowerSeries.smul_eq_C_mul]
  rfl
end Formalism.L2.Th1.D.BrC
