-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.lowSpan_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:43.145517+00:00
-- url     : https://prove2.me/submissions/5502f4e9-856f-4a68-8599-2c3513795fe4

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds

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
theorem _root_.solution (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) (c d : Fin q) (h : d < c) :
    ∀ y ∈ lowSpan T κ, T c d y ∈ lowSpan T κ := by
  intro y hy
  have : (lowSpan T κ).map (T c d) ≤ lowSpan T κ := by
    unfold lowSpan
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span (LowW.step c d x h hx)
  exact this (Submodule.mem_map_of_mem hy)
end Formalism.CohomologicalDescent.LP
