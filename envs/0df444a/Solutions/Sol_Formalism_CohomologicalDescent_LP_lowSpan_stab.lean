-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.lowSpan_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:17:11.428518+00:00
-- url     : https://prove2.me/submissions/2f31e0c3-e067-471f-892d-ccb1334c2720

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds
import Theorems.Thm_Formalism_CohomologicalDescent_LP_lowW_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) : Stab T (lowSpan T κ) := by
  intro a b y hy
  have : (lowSpan T κ).map (T a b) ≤ lowSpan T κ := by
    rw [lowSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact lowW_all T hT κ x hx a b
  exact this (Submodule.mem_map_of_mem hy)
end Formalism.CohomologicalDescent.LP
