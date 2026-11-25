-- Prove2me | solution 1 for Formalism.L2.Th1.D.BrC.lawLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:40:25.075341+00:00
-- url     : https://prove2.me/submissions/c4b9afb0-5b17-45fb-9d35-8fbd50b831dd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog)
namespace BrC
section Alg
variable {K : Type} [Field K]
private theorem lgF_zero_lemma (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp
private theorem lgF_one_lemma_2 {l : ℕ} (hl : 2 ≤ l) : PowerSeries.coeff 1 (lgF K l) = 1 := by
  have h1 : l ^ 2 ≠ 1 := by nlinarith
  rw [lgF, PowerSeries.coeff_mk]
  simp [Finset.sum_range_succ, h1, h1.symm]
end Alg
section Cont
variable {K : Type} [Field K]
end Cont
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable [CharZero K]
end Normed
end BrC
end Formalism.L2.Th1.D
end
end

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
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog l F) :
    Formalism.L2.Th1.B.LawLog F (lgF K l) := by
  exact ⟨hF.1, hF.2.1, lgF_zero_lemma l, lgF_one_lemma_2 hl, hF.2.2⟩
end Formalism.L2.Th1.D.BrC
