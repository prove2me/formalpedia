-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.c_prime_le_short_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:36.974163+00:00
-- url     : https://prove2.me/submissions/d352a83a-9fa9-459e-98f2-6ec6ccf38937

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_harmonic_positive_log_holds


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
theorem _root_.solution : CPrimeLeShort6 := by
  intro l k j t q h N' ecl xm xp mB I hl hI
  unfold cPrime cShort6 labelSumBoundPos
  have h1 := (harmonic_positive_log_holds l h I hI).1
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have h3 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg _; linarith) hl1
  have h4 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ (q : ℝ) + 2 * (j : ℝ))
  linarith
end Formalism.CohomologicalDescent.ShortWeightBounds
