-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.short_bound_nonneg_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:06.280795+00:00
-- url     : https://prove2.me/submissions/17067e1c-d484-41c0-8469-fdfc5709e6c7

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_indexIntegral_nonneg_of_params
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_gated_min_nonneg_of_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution : Short6Nonneg := by
  intro l k j t q h N' ecl xm xp mB I hl hx hI
  unfold cShort6
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h1 : 0 ≤ ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) hl1)
  have h2 : 0 ≤ (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (div_nonneg (by exact_mod_cast sub_nonneg.mpr hx) (Nat.cast_nonneg _))
      (indexIntegral_nonneg_of_params l xm xp mB))
  have h3 := gated_min_nonneg_of_nonneg l k t (xm - mB) I hI
  have h4 : 0 ≤ (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))) := by
    have := Real.posLog_nonneg (x := (h : ℝ) / (l : ℝ))
    exact mul_nonneg (div_nonneg hI (Nat.cast_nonneg _)) (by linarith)
  have h5 : (0 : ℝ) ≤ ecl := Nat.cast_nonneg _
  linarith
end Formalism.CohomologicalDescent.ShortWeightBounds
