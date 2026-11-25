-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.shape_a_real_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:10.912047+00:00
-- url     : https://prove2.me/submissions/10b10194-e43d-4095-9507-2b302130329d

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weights_strictAnti
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weights_antitone_le
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_abs_weight_sub_near_translation_le
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_upper_translation_le_floor_height
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weight_le_upper_translation_of_thick
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_toNat_cast_real_of_nonneg

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
theorem _root_.solution : ShapeAReal := by
  intro P hP hL ι W hW τ hτ
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  have hx := upper_translation_le_floor_height P hP W hW τ hτ
  have hw := hW.window τ
  have hS : 0 ≤ W.xp τ - W.xm τ := by have := hw.2.1; omega
  have hE : 0 ≤ W.U P τ (kc P) - W.U P τ (P.Nr - 1) := by
    have := weights_antitone_le P W hW τ (kc P) (P.Nr - 1) (by omega) (by omega)
    omega
  refine ⟨⟨?_, ?_, by omega, ?_, ?_⟩, ?_, ?_⟩
  · intro a b hab
    exact weights_strictAnti P W hW τ a b hab b.isLt
  · intro a
    refine ⟨weight_nonneg' P W τ a a.isLt, ?_⟩
    have := weight_le_upper_translation_of_thick P hP hL W hW τ hτ a a.isLt
    omega
  · intro a ha
    have h1 := hW.cloud τ a ha
    rw [Int.toNat_of_nonneg hS]
    exact ⟨h1.1, by omega⟩
  · intro a ha
    rw [Int.toNat_of_nonneg hE]
    have h1 := weights_antitone_le P W hW τ a (P.Nr - 1) (by have := a.isLt; omega) (by omega)
    have h2 := weights_antitone_le P W hW τ (kc P) a ha a.isLt
    exact ⟨h1, by omega⟩
  · rw [toNat_cast_real_of_nonneg _ hS]
    push_cast
    linarith [hw.1, hw.2.2]
  · rw [toNat_cast_real_of_nonneg _ hE]
    have h1 := abs_le.mp (abs_weight_sub_near_translation_le P hP W hW τ (kc P) le_rfl (by omega))
    have h2 := abs_le.mp (abs_weight_sub_near_translation_le P hP W hW τ (P.Nr - 1) (by omega) (by omega))
    push_cast
    linarith [h1.2, h2.1]
end Formalism.CohomologicalDescent.ShortWeightBounds
