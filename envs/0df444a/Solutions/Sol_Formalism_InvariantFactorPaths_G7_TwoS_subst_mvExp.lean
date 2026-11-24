-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.subst_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:59.815375+00:00
-- url     : https://prove2.me/submissions/78d26584-02d3-4e16-b52a-b42b7085b87d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS
open Formalism.InvariantFactorPaths.G7.TwoS
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {K ι κ : Type} [NormedField K] [CharZero K] {ψ : ι → MvPowerSeries κ K}
    (hψ : MvPowerSeries.HasSubst ψ) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst ψ (mvExp g) = mvExp (MvPowerSeries.subst ψ g) := by
  unfold mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero hg).const hψ]
end Formalism.InvariantFactorPaths.G7.TwoS
