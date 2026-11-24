-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.coeff_posW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:59.411909+00:00
-- url     : https://prove2.me/submissions/bb2ae6f2-1435-497c-b11f-bb22670a12ff

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_sPos
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
variable {K : Type} [Field K]
variable {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution [NeZero ν] (p : ℕ) (w : ZMod (2 * ν) → K) (ab : Fin r0 × Fin r1)
    (n : ZV ν r0 r1 →₀ ℕ) :
    MvPowerSeries.coeff n (posW p w ab) = ∑ l ∈ range (n.degree + 1), (-1) ^ l *
      MvPowerSeries.coeff n (∑ s : ZMod (2 * ν), MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
        (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := by
  simp only [posW, map_sum, MvPowerSeries.coeff_C_mul, coeff_sPos, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight (2 * (l : ZMod (2 * ν))))]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, MvPowerSeries.coeff_X_pow]
  split_ifs <;> ring
end Formalism.InvariantFactorPaths.G7.TwoS
