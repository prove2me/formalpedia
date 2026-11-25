-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.subst_tensor4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:18.209643+00:00
-- url     : https://prove2.me/submissions/b8d88714-4ac2-4e80-9873-fd42e866d90e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst


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
theorem _root_.solution {ρ : Type} (T : MvPowerSeries n K) {φ : Fin 4 × n → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (tensor4 T) = ∏ a : Fin 4, MvPowerSeries.subst (fun i => φ (a, i)) T := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  unfold tensor4
  rw [← MvPowerSeries.coe_substAlgHom h, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _) h]
  congr 1
  funext i
  exact MvPowerSeries.subst_X h _
end Formalism.L2.Th1.H.FormalGroupLawNegation
