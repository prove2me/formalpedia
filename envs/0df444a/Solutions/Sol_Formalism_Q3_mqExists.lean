-- Prove2me | solution 1 for Formalism.Q3.mqExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:09.384331+00:00
-- url     : https://prove2.me/submissions/78753be7-6043-4cd1-8c12-931a299ae471

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Theorems.Thm_Formalism_Q3_exists_square_roots_closure
import Theorems.Thm_Formalism_Q3_adjoin_subtype_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution : MQExists := by
  intro k a
  obtain ⟨β, hβ⟩ := exists_square_roots_closure a
  set K := IntermediateField.adjoin ℚ (Set.range β) with hK
  have hint : ∀ x ∈ Set.range β, IsIntegral ℚ x := by
    rintro _ ⟨i, rfl⟩
    refine ⟨X ^ 2 - C ((a i : ℚ)), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hβ i, map_intCast, sub_self]
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hint
  haveI : NumberField K := ⟨⟩
  let α' : Fin k → K := fun i => ⟨β i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  refine ⟨K, inferInstance, inferInstance, α', ?_, ?_⟩
  · intro i
    apply Subtype.ext
    simp [α', hβ i]
  · exact adjoin_subtype_top K β hK α' (fun i => rfl)
end Formalism.Q3
