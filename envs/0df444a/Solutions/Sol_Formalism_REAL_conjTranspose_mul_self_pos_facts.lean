-- Prove2me | solution 1 for Formalism.REAL.conjTranspose_mul_self_pos_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:03.889961+00:00
-- url     : https://prove2.me/submissions/651aa1e3-5b98-476e-802b-0079a19907db

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_spectrum_pos_of_posSemidef_unit
import Theorems.Thm_Formalism_REAL_indefinite_unitary_preserves_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g) ∧ ∀ x ∈ spectrum ℝ (gᴴ * g), 0 < x := by
  have hu : IsUnit g := (indefinite_unitary_preserves_form hg).2
  refine ⟨Matrix.isHermitian_conjTranspose_mul_self g, ?_, ?_⟩
  · exact (IsUnit.star hu).mul hu
  · exact spectrum_pos_of_posSemidef_unit (Matrix.posSemidef_conjTranspose_mul_self g) ((IsUnit.star hu).mul hu)
end Formalism.REAL
