-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:06.832846+00:00
-- url     : https://prove2.me/submissions/c23e8263-6476-4509-b816-9b3a9be1db8f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (P : Par) (x : A P) (hx : x ∈ fnsA P) : ∃ f fb, x = sc P (fnP f fb) := by
  rcases hx with ((((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩) | hx)
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
end Formalism.FourierDecayAlt.P.Mx2
