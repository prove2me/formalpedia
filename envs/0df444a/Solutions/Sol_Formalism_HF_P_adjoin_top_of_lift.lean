-- Prove2me | solution 1 for Formalism.HF.P.adjoin_top_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:56.666044+00:00
-- url     : https://prove2.me/submissions/16238c0f-1535-4529-9e09-a09471a487c5

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution {E : Type} [Field E] [Algebra ℚ E] (K : IntermediateField ℚ E) (S : Set K)
    (h : adjoin ℚ (Subtype.val '' S) = K) : adjoin ℚ S = ⊤ := by
  have key : @IntermediateField.adjoin ℚ _ K _ K.algebra' S = ⊤ := by
    apply IntermediateField.lift_injective K
    rw [IntermediateField.lift_adjoin, h, IntermediateField.lift_top]
  have gen : ∀ (inst : Algebra ℚ K), inst = K.algebra' →
      @IntermediateField.adjoin ℚ _ K _ inst S = ⊤ := by
    rintro inst rfl
    exact key
  exact gen _ (Subsingleton.elim _ _)
end Formalism.HF.P
