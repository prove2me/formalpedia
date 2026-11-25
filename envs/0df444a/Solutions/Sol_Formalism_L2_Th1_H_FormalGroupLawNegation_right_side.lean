-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.right_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:39:11.160177+00:00
-- url     : https://prove2.me/submissions/c1ff1c3f-513b-4ccf-bbfc-201db02b6ddf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_constantCoeff_inVar_eq_zero


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)
open Formalism.L2.Th1.H.FormalGroupLawNegation
variable {K : Type} [Field K] {n : Type} [Fintype n]
namespace Formalism.L2.Th1.H.FormalGroupLawNegation
theorem _root_.solution {lg : PowerSeries K} (hlg : PowerSeries.constantCoeff lg = 0) {m κ : Type} [Fintype m]
    (S : Finset κ) (r : κ → K) (f : κ → m → PowerSeries K) :
    MvPowerSeries.subst (fun w => at1 w lg) (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w ((f x w).subst lg) := by
  have hat : ∀ s : m, MvPowerSeries.constantCoeff (at1 s lg : MvPowerSeries m K) = 0 :=
    fun s => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero s hlg
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hat
  rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod, MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_C]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [subst_single_var _ _ hat]
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.subst_subst hlg (MvPowerSeries.constantCoeff_X w)]
end Formalism.L2.Th1.H.FormalGroupLawNegation
