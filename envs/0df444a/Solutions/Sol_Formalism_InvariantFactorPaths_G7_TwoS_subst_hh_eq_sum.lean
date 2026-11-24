-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.subst_hh_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:59.820041+00:00
-- url     : https://prove2.me/submissions/37769e61-fcbc-479e-b1ea-bbcbba348733

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
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ} [NeZero ν]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {τ E : Type} [Fintype E] (p : ℕ) (c c' : K)
    {φ : Bool × E → MvPowerSeries τ K} (hs : MvPowerSeries.HasSubst φ) :
    MvPowerSeries.subst φ (hh1 (E := E) p c c') =
      ∑ e : E, (MvPowerSeries.C c * φ (false, e) * φ (true, e) ^ p -
        MvPowerSeries.C c' * φ (false, e) ^ p * φ (true, e)) := by
  have hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r :=
    fun r => (MvPowerSeries.substAlgHom hs).commutes r
  rw [hh1, ← MvPowerSeries.coe_substAlgHom hs]
  simp only [map_sum, map_sub, map_mul, map_pow, hC, MvPowerSeries.substAlgHom_X]
end Formalism.InvariantFactorPaths.G7.TwoS
