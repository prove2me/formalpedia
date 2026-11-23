-- Prove2me | solution 1 for Formalism.FN.SuccessiveMinima.exists_pos_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.010652+00:00
-- url     : https://prove2.me/submissions/25e1feb1-4a01-49fa-bd6d-14c1a15cf576

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
import Theorems.Thm_Formalism_FN_SuccessiveMinima_mem_smul_iff_gauge
import Theorems.Thm_Formalism_FN_SuccessiveMinima_finite_lat_inter
import Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_gap

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
theorem _root_.solution (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → t < m →
      Submodule.span ℝ ((L : Set E) ∩ t • K) = ⊥ := by
  have hK : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero hK
  set B : Set E := {u | u ∈ (L : Set E) ∩ K ∧ u ≠ 0} with hB
  have hBfin : B.Finite := (finite_lat_inter L hKc.isBounded).subset fun u hu => hu.1
  obtain ⟨m, hm0, hm1, hmB⟩ := exists_gap (gauge K) hBfin zero_lt_one
    fun u hu => (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu.2
  refine ⟨m, hm0, fun t ht htm => Submodule.span_eq_bot.mpr ?_⟩
  rintro u ⟨huL, hut⟩
  have hgt : gauge K u ≤ t := (mem_smul_iff_gauge hKc hKv hK0 ht u).mp hut
  by_contra hu
  have huK : u ∈ K := by
    have := (mem_smul_iff_gauge hKc hKv hK0 zero_le_one u).mpr (by linarith)
    rwa [one_smul] at this
  have := hmB u ⟨⟨huL, huK⟩, hu⟩
  linarith
end Formalism.FN.SuccessiveMinima
