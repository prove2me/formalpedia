-- Prove2me | solution 1 for Formalism.FN.SuccessiveMinima.exists_gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:40.274935+00:00
-- url     : https://prove2.me/submissions/59671e43-6d11-4cb1-a127-60e62e34c99b

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism Formalism.FN Formalism.FN.SuccessiveMinima
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.FN.SuccessiveMinima
theorem _root_.solution {α : Type*} (f : α → ℝ) {B : Set α} (hB : B.Finite) {c T : ℝ} (hcT : c < T)
    (h : ∀ u ∈ B, c < f u) : ∃ m, c < m ∧ m ≤ T ∧ ∀ u ∈ B, m ≤ f u := by
  obtain ⟨m, hmS, hmin⟩ := Set.exists_min_image (insert T (f '' B)) id
    ((hB.image f).insert T) ⟨T, Set.mem_insert _ _⟩
  refine ⟨m, ?_, hmin T (Set.mem_insert _ _), fun u hu => hmin (f u) (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)⟩
  rcases hmS with rfl | ⟨u, hu, rfl⟩
  · exact hcT
  · exact h u hu
end Formalism.FN.SuccessiveMinima
