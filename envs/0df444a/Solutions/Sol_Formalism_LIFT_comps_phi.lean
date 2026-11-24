-- Prove2me | solution 1 for Formalism.LIFT.comps_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:32:03.32086+00:00
-- url     : https://prove2.me/submissions/9f48f886-a056-4d4c-a599-71a7c580b8ff

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)
namespace Formalism.LIFT
theorem _root_.solution (hℓ : 0 < ℓ) {a : A} (ha : a ∈ aa) : Comps φA ε aa ℓ (φA a) := by
  refine ⟨fun i => if (i : ℕ) = 0 then a else 0, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ha
    · exact aa.zero_mem
  · rw [Fintype.sum_eq_single ⟨0, hℓ⟩]
    · simp
    · intro i hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]
end Formalism.LIFT
