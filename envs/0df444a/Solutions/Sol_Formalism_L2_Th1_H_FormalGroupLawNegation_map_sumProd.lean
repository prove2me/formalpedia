-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.map_sumProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:10:23.919535+00:00
-- url     : https://prove2.me/submissions/28516f0e-bd71-463f-b392-b36105b562c1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_inVar


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
theorem _root_.solution {κ : Type} (S : Finset κ) (r : κ → K₀) (f : κ → n → PowerSeries K₀) :
    MvPowerSeries.map ι (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (ι (r x)) * ∏ w, at1 w (PowerSeries.map ι (f x w)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod, MvPowerSeries.map_C]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  exact Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_inVar ι w _
end Formalism.L2.Th1.H.FormalGroupLawNegation
