-- Prove2me | solution 1 for Formalism.REAL.symmetricSliceMixedCasimir_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:31.788098+00:00
-- url     : https://prove2.me/submissions/9a61f0db-7990-48c8-83bd-b9bf2777cf69

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_mixedCasimir_mul_permuteFactors
import Theorems.Thm_Formalism_REAL_mem_symmetricArrays
import Theorems.Thm_Formalism_REAL_firstPositionSlice_positionMixedCasimir_zero
import Theorems.Thm_Formalism_REAL_inner_permutePositions
import Theorems.Thm_Formalism_REAL_inner_eq_sum_firstPositionSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution : OmSymSlice := by
  intro V _ _ n ε E j F
  refine ⟨fun hF i => ?_, ?_⟩
  · rw [mem_symmetricArrays] at hF
    have h1 : OmS ε E i (permArr V n (Equiv.swap 0 i) F) =
        permArr V n (Equiv.swap 0 i) (OmS ε E ((Equiv.swap 0 i).symm i) F) :=
      LinearMap.congr_fun (mixedCasimir_mul_permuteFactors ε E (Equiv.swap 0 i) i) F
    rw [hF, Equiv.symm_swap, Equiv.swap_apply_right] at h1
    rw [h1]
    calc _ = ⟪permArr V n (Equiv.swap 0 i) F, permArr V n (Equiv.swap 0 i) (OmS ε E 0 F)⟫_ℂ := by
          rw [hF]
      _ = _ := inner_permutePositions _ _ _
  · rw [inner_eq_sum_firstPositionSlice]
    simp only [firstPositionSlice_positionMixedCasimir_zero]
end Formalism.REAL
