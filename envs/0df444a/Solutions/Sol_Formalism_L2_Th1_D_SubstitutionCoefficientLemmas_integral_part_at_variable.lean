-- Prove2me | solution 1 for Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.integral_part_at_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:51.381983+00:00
-- url     : https://prove2.me/submissions/099fc6d9-f86b-43e0-a61a-42b0984c83a0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_artin_hasse_log_frobenius_shift
import Theorems.Thm_P2M_Formalism_L2_Th1_D_KernelCokernelKilling_integral_X__2606e57c7606


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
namespace Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
theorem _root_.solution {l : ℕ} (hp : l.Prime) (σ : K →+* K) (x : Fin 2) : IP l σ (at1 x (lgF K l)) :=
  ⟨constantCoeff_inVar_eq_zero _ (cc_lgF hp.two_le), by
    rw [TranslateJetMomentLawAnyIdempotentLevel.artin_hasse_log_frobenius_shift hp]
    exact KernelCokernelKilling.integral_X' _⟩
end Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
