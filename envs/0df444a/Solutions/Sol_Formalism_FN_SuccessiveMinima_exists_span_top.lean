-- Prove2me | solution 1 for Formalism.FN.SuccessiveMinima.exists_span_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.725913+00:00
-- url     : https://prove2.me/submissions/ffb762c3-66fb-4611-a230-187238db742d

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
import Theorems.Thm_Formalism_FN_SuccessiveMinima_mem_smul_iff_gauge

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
variable (L : Submodule ℤ E) [DiscreteTopology L] {K : Set E}
namespace Formalism.FN.SuccessiveMinima
theorem _root_.solution [IsZLattice ℝ L] (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) :
    ∃ T : ℝ, 0 ≤ T ∧ Submodule.span ℝ ((L : Set E) ∩ T • K) = ⊤ := by

  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set E)
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨M, hM⟩ := (hbfin.image (gauge K)).bddAbove
  refine ⟨max M 0, le_max_right _ _, eq_top_iff.mpr ?_⟩
  have hLtop : Submodule.span ℝ (L : Set E) = ⊤ := IsZLattice.span_top
  rw [← hLtop, ← hbspan]
  refine Submodule.span_mono fun x hx => ⟨hbL hx, ?_⟩
  refine (mem_smul_iff_gauge hKc hKv hK0 (le_max_right _ _) x).mpr ?_
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
end Formalism.FN.SuccessiveMinima
