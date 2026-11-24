-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionSums.subst_sumE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:52.27097+00:00
-- url     : https://prove2.me/submissions/42111e55-ab14-4561-b048-af0a335a3adf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums
namespace Formalism.L2.Th1.D.BiextensionSums
theorem _root_.solution {K ι κ : Type} [Field K] [Fintype ι] {N0 N1 : ℕ}
    {Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries κ K}
    (h0 : ∀ x, constantCoeff (Xt x) = 0) (be : MvPowerSeries (Fin 2) K) :
    subst Xt (sumE be) = ∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be := by
  have hX : HasSubst Xt := hasSubst_of_constantCoeff_zero h0
  unfold sumE
  rw [subst_sum hX]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (by intro a; simp)) hX]
  congr 1
  funext a
  rw [subst_X hX]
  fin_cases a <;> rfl
end Formalism.L2.Th1.D.BiextensionSums
