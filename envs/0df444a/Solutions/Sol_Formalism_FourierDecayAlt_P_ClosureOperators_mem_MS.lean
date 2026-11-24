-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.mem_MS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:53:50.092934+00:00
-- url     : https://prove2.me/submissions/8e5b216c-7b20-43cb-824d-3eb70ba4ad3d

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mono_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) : v ∈ MS f v := by
  apply Submodule.subset_span
  exact ⟨fun _ => 0, by simp [mono_zero]⟩
end Formalism.FourierDecayAlt.P.ClosureOperators
