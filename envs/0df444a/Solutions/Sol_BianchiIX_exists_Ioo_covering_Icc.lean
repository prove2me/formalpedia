-- Prove2me | solution 1 for BianchiIX.exists_Ioo_covering_Icc
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:33:45.965248+00:00
-- url     : https://prove2.me/submissions/aa3207f7-f5eb-4752-842a-01129dd73e90

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- A closed real interval in an open set has an open interval neighborhood in that set. -/
theorem solution {s t : ℝ} {U : Set ℝ} (hst : s ≤ t)
    (hU : IsOpen U) (hsub : Icc s t ⊆ U) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ Ioo l r ⊆ U := by
  obtain ⟨l, v, hs, hl⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hsub ⟨le_rfl, hst⟩))
  obtain ⟨u, r, ht, hr⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hsub ⟨hst, le_rfl⟩))
  refine ⟨l, r, hs.1, ht.2, ?_⟩
  intro x hx
  by_cases hxs : x < s
  · exact hl ⟨hx.1, hxs.trans hs.2⟩
  by_cases htx : t < x
  · exact hr ⟨ht.1.trans htx, hx.2⟩
  exact hsub ⟨le_of_not_gt hxs, le_of_not_gt htx⟩
