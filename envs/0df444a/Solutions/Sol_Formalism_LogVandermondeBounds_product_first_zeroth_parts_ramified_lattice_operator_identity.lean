-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramified_lattice_operator_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:07.188991+00:00
-- url     : https://prove2.me/submissions/1c016105-80a3-4090-930b-6ec808f11161

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_opU_eq_opD
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmP_eq_nmV
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_ram_V

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution : UnitsSumZero := by
  intro k _ _ _ r R _
  refine ⟨fun ψ h => ram_V ψ h, fun φ h => ?_⟩
  have h' : ∀ y, y ≠ 0 → nmV φ y = 0 := fun y hy => by rw [← nmP_eq_nmV]; exact h y hy
  obtain ⟨h1, h2, h3⟩ := ram_V φ h'
  refine ⟨fun x => ?_, h2, fun hr f hf => ?_⟩
  · rw [← nmP_eq_nmV, ← opU_eq_opD]; exact h1 x
  · rw [← opU_eq_opD φ, opU_eq_opD (opU φ)]; exact h3 hr f hf
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
