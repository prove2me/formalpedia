-- Prove2me | solution 1 for Formalism.REAL.compact_span_eq_lowering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:37.054479+00:00
-- url     : https://prove2.me/submissions/48f9cdbc-b42d-42f4-860c-dc8048c723a0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_mem_compact_span_self
import Theorems.Thm_Formalism_REAL_compact_span_stable
import Theorems.Thm_Formalism_REAL_compact_span_le_stable
import Theorems.Thm_Formalism_REAL_self_mem_lowering_span
import Theorems.Thm_Formalism_REAL_lowering_span_stable

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
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    kSpan ε F x = lowSpan ε F x := by
  apply le_antisymm
  · exact compact_span_le_stable (self_mem_lowering_span x) (lowering_span_stable h hx)
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    induction w with
    | nil => exact mem_compact_span_self x
    | cons p w ih =>
      exact compact_span_stable x p.1 p.2 (hw p List.mem_cons_self).1 _
        (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
end Formalism.REAL
