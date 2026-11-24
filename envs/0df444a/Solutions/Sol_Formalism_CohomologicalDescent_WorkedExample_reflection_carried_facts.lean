-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.reflection_carried_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:04:49.926096+00:00
-- url     : https://prove2.me/submissions/52e6ab4c-7440-4f10-a972-00aed4b89cfd

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution {ι : Type} {N : ℕ} (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (ep : ι → ι)
    (J : ι → Fin N → ℤ) (botJ : ι → ℤ) (hR : D.Refl σ h t) (hC : D.Carried ep J botJ) :
    (∀ i, ep (ep i) = i) ∧ (∀ i, σ (ep i) = ep (σ i)) ∧ (∀ i, J i = D.U' (ep i)) ∧
      (∀ i, botJ i = D.bot (ep i)) := by
  obtain ⟨hinv, hcom, _⟩ := hR
  obtain ⟨hep, hJ, hb⟩ := hC
  have h1 : ∀ i, ep (ep i) = i := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hinv
  have h2 : ∀ i, σ (ep i) = ep (σ i) := by
    rcases hep with rfl | rfl
    · intro i; rfl
    · exact hcom
  refine ⟨h1, h2, fun i => ?_, fun i => ?_⟩
  · rw [← hJ (ep i), h1]
  · rw [← hb (ep i), h1]
end Formalism.CohomologicalDescent.WorkedExample
