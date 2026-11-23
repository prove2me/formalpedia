-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.rk_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:38.204393+00:00
-- url     : https://prove2.me/submissions/cc26c2f0-e61b-456c-81cf-55bf9abd79cf

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_eig
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mul_mem_FI
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_finrank_le_of_map_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_exists_delta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (A : FI E) (s : ℕ) : finrank ℤ (eig E A s) ≤ finrank ℤ (eig E A (s + 1)) := by
  obtain ⟨δ, h0, hδ⟩ := exists_delta E
  refine finrank_le_of_map_le E (LinearMap.mulLeft ℤ (δ : E)) (mul_right_injective₀ h0) _ _ ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨ht1, ht2⟩ := (mem_eig E A s t).mp ht
  rw [mem_eig, LinearMap.mulLeft_apply]
  refine ⟨mul_mem_FI E A δ t ht1, ?_⟩
  rw [map_mul, hδ, pow_succ]
  linear_combination (δ : E) * ht2
end Formalism.FourierDecayAlt.P.S6x3
