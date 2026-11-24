-- Prove2me | solution 1 for Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.right_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:26.567875+00:00
-- url     : https://prove2.me/submissions/1feff5b5-5c4b-4037-a59e-bb48fb38259f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
import Theorems.Thm_Formalism_L2_Th1_D_Pair_addC_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_D_Pair_log_mul
import Theorems.Thm_Formalism_L2_Th1_D_expSpec


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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) {β : K} {e : PowerSeries K} (he : IsMul l β e)
    (be0 : MvPowerSeries (Fin 2) K) :
    subst ![at1 (0 : Fin 2) (lgF K l), C β * at1 (1 : Fin 2) (lgF K l)] (addC l be0) =
      subst ![X 0, at1 (1 : Fin 2) e] be0 := by
  have h := addC_log expSpec hl (a := X 0) (b := at1 (1 : Fin 2) e) (constantCoeff_X 0)
    (constantCoeff_inVar_eq_zero _ he.1) be0
  have h1 : PowerSeries.subst (at1 (1 : Fin 2) e) (lgF K l) = C β * at1 (1 : Fin 2) (lgF K l) :=
    log_mul he (constantCoeff_X 1)
  rw [h1] at h
  exact h
end Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
