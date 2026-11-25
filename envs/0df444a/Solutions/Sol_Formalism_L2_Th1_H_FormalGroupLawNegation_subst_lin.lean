-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.subst_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:32.336538+00:00
-- url     : https://prove2.me/submissions/2a00ab20-9e25-432f-9324-6190009625cd

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
theorem _root_.solution {σ ρ m : Type} [Finite σ] [Fintype m] (c : m → K) (u : m → MvPowerSeries σ K)
    {φ : σ → MvPowerSeries ρ K} (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (∑ j, MvPowerSeries.C (c j) * u j) =
      ∑ j, MvPowerSeries.C (c j) * MvPowerSeries.subst φ (u j) := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_C]
end Formalism.L2.Th1.H.FormalGroupLawNegation
