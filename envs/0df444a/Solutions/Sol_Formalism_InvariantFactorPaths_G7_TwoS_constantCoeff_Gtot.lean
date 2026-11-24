-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.constantCoeff_Gtot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:40.628099+00:00
-- url     : https://prove2.me/submissions/e7f9c6db-fe28-45ce-83c6-64dd3c00ef87

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_Gser
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
theorem _root_.solution {K E : Type} [Field K] [Fintype E] {p : ℕ} (hp : p ≠ 0)
    (c c' ϖ : K) : MvPowerSeries.constantCoeff (Gtot (E := E) p c c' ϖ) = 0 := by
  unfold Gtot
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have h0 : ∀ a : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.C ϖ *
      (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
        MvPowerSeries (Bool × E) K)) = 0 := fun a => by simp
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 (constantCoeff_Gser hp c c')
end Formalism.InvariantFactorPaths.G7.TwoS
