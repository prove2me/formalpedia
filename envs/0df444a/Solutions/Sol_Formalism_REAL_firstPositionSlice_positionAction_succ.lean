-- Prove2me | solution 1 for Formalism.REAL.firstPositionSlice_positionAction_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:05.83717+00:00
-- url     : https://prove2.me/submissions/17b8e15b-854a-4920-979c-ff41c60374f2

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext
import Theorems.Thm_Formalism_REAL_firstPositionSlice_apply
import Theorems.Thm_Formalism_REAL_firstPositionSlice_positionAction_succ_apply

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (α' : Fin j → Fin n × Fin n) (k : Fin j) (a b : Fin n)
    (F : Arr V n (j+1)) :
    sliceLin V n α' (factorAction k.succ a b F) =
      (if (α' k).1 = a then sliceLin V n (Function.update α' k (b, (α' k).2)) F else (0 : Arr V n 1)) -
      (if (α' k).2 = b then sliceLin V n (Function.update α' k ((α' k).1, a)) F else (0 : Arr V n 1)) := by
  refine indexArray_ext fun β => (firstPositionSlice_positionAction_succ_apply α' k a b F β).trans ?_
  have hf : ∀ X : Arr V n 1, X β =
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) β ∘ₗ arrOf V n 1) X :=
    fun X => rfl
  rw [hf, map_sub, ← hf, ← hf]
  congr 1
  · by_cases h1 : (α' k).1 = a
    · rw [if_pos h1, if_pos h1, firstPositionSlice_apply]
    · rw [if_neg h1, if_neg h1, hf, map_zero]
  · by_cases h2 : (α' k).2 = b
    · rw [if_pos h2, if_pos h2, firstPositionSlice_apply]
    · rw [if_neg h2, if_neg h2, hf, map_zero]
end Formalism.REAL
