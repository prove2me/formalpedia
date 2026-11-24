-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_lattice_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:24.101847+00:00
-- url     : https://prove2.me/submissions/d66f37c5-5d22-48e0-b481-baf3056ee6c4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_deltaLTw
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) : (1 : MvPolynomial _ K) ∈ Dl0 R m 0 Λ := by
  unfold Dl0
  rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  simp only [Submodule.mem_iInf]
  intro g _
  exact one_mem_deltaLTw R K m g
end Formalism.MainNotions.G.Inhab
