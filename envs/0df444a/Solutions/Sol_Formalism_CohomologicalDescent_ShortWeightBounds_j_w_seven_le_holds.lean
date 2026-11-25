-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.j_w_seven_le_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:30.21666+00:00
-- url     : https://prove2.me/submissions/e35065bb-81f1-4ada-8a92-3f16585adcab

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_short_bound_le_coarse_holds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_short_bound_nonneg_holds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_coarse_le_c_w_holds

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
theorem _root_.solution : CoarseWeightBoundLe := by
  intro P hH hL ι _ _ W hW J l hl
  constructor
  · unfold Wts.JW Wts.coarseWeightBound
    apply Finset.sum_le_sum
    intro τ _
    unfold cTau
    split_ifs
    · exact min_le_min le_rfl (Nat.floor_le_floor (short_bound_le_coarse_holds _ _ _ _ _ _ _ _ _ _ _ _).2)
    · exact le_rfl
  · unfold Wts.coarseWeightBound
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro τ _
    by_cases hτ : τ ∈ W.T2
    · have hτ' : τ ∈ (W.sizeData₂ P J).T2 := hτ
      rw [if_pos hτ']
      unfold cTau
      rw [if_pos hτ, Nat.cast_min]
      apply min_le_min le_rfl
      have h1 := coarse_le_c_w_holds P hH hL ι W hW J τ hτ l hl
      have h2 := short_bound_nonneg_holds l (kc P) (W.j τ) P.t (W.q τ) (h0 P) P.Nr (W.ecl P τ l) (W.xm τ)
        (W.xp τ) (W.top P τ) (W.iW P l τ : ℝ) (by omega) (hW.window τ).2.1 (Nat.cast_nonneg _)
      have h3 := (short_bound_le_coarse_holds l (kc P) (W.j τ) P.t (W.q τ) (h0 P) P.Nr (W.ecl P τ l) (W.xm τ)
        (W.xp τ) (W.top P τ) (W.iW P l τ : ℝ)).2
      exact (Nat.floor_le (h2.trans h3)).trans h1
    · have hτ' : τ ∉ (W.sizeData₂ P J).T2 := hτ
      rw [if_neg hτ']
      unfold cTau
      rw [if_neg hτ]
      exact le_rfl
end Formalism.CohomologicalDescent.ShortWeightBounds
