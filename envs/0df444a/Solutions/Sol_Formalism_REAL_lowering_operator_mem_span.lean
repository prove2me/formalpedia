-- Prove2me | solution 1 for Formalism.REAL.lowering_operator_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:01.759314+00:00
-- url     : https://prove2.me/submissions/9c25fe44-11b9-4e9d-b052-e3764631fd32

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_lowering_word_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution {x : V} {c d : Fin n} (hcd : ε c = ε d) (hdc : d < c) {z : V}
    (hz : z ∈ lowSpan ε F x) : F c d z ∈ lowSpan ε F x := by
  have : lowSpan ε F x ≤ (lowSpan ε F x).comap (F c d) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    show F c d (ew F w x) ∈ lowSpan ε F x
    refine lowering_word_mem_span x ((c, d) :: w) ?_
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hcd, hdc⟩
    · exact hw p hp
  exact this hz
end Formalism.REAL
