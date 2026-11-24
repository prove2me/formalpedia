-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.linkage_depth_eq_sum_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:35.818629+00:00
-- url     : https://prove2.me/submissions/16a1fe54-d475-44fe-9cdf-7cb22204f838

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_depth_as_weight_sum_holds


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
theorem _root_.solution (N k j t q : ℕ) (hN : k + j + t + q = N) (lam : ℕ → ℕ) (w : Fin N → ℕ)
    (U U' : Fin (k + j + t + q) → ℤ) (hU : ∀ a, U a = UN N lam a)
    (hU' : ∀ (a : Fin (k + j + t + q)) (a' : Fin N), (a : ℕ) = (a' : ℕ) →
      U' a = (w a' : ℤ) + (N : ℤ) - 1 - ((a : ℕ) : ℤ)) :
    depth2 (res N (varpi (k + j))) (res N lam) w =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) := by
  subst hN
  rw [depth_as_weight_sum_holds]
  apply Finset.sum_congr rfl
  intro a _
  rw [hU, hU' a a rfl]
end Formalism.CohomologicalDescent.ShortWeightBounds
