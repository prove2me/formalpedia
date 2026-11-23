-- Prove2me | solution 1 for Formalism.FN.GjScaling.mem_span_basisFun_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.013567+00:00
-- url     : https://prove2.me/submissions/05637431-7670-4fbe-96a6-b4e75c81b19f

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]
namespace Formalism.FN.GjScaling
theorem _root_.solution (x : ι → ℝ) :
    x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ x ∈ Zv ι := by
  rw [Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, Int.coe_castRingHom, Zv,
    Set.mem_setOf_eq]
  constructor
  · intro h i
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, hm.symm⟩
  · intro h i
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, hm.symm⟩
end Formalism.FN.GjScaling
