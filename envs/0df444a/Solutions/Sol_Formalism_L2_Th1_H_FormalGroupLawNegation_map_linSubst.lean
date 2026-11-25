-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:54:10.318587+00:00
-- url     : https://prove2.me/submissions/715ab1fc-f9f8-4887-b432-b7b7b9c2e4a8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_cc_lin
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_LT_LTL_cc_lin


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
variable {K₀ K : Type} [Field K₀] [Field K] (ι : K₀ →+* K) {n : Type} [Fintype n]
namespace Formalism.L2.Th1.H.FormalGroupLawNegation
theorem _root_.solution {m : Type} [Finite m] (M : Matrix m n K₀) (T : MvPowerSeries m K₀) :
    MvPowerSeries.map ι (linSubst M T) = linSubst (M.map ι) (MvPowerSeries.map ι T) := by
  have hs : MvPowerSeries.HasSubst
      (fun i => ∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K₀)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  unfold linSubst
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext i
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, Matrix.map_apply]
end Formalism.L2.Th1.H.FormalGroupLawNegation
