-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_largest_moved_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:54.332792+00:00
-- url     : https://prove2.me/submissions/6374fb5b-76d4-4ab4-a2ba-e99a49ebb20d

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {N : ℕ} (σ : Equiv.Perm (Fin N)) (hσ : σ ≠ 1) :
    ∃ j0, σ j0 < j0 ∧ ∀ j, j0 < j → σ j = j := by
  classical
  obtain ⟨j1, hj1⟩ : ∃ j, σ j ≠ j := by
    by_contra h
    push_neg at h
    exact hσ (Equiv.ext fun x => by simpa using h x)
  set S := Finset.univ.filter fun j => σ j ≠ j with hSdef
  have hS : S.Nonempty := ⟨j1, by simp [S, hj1]⟩
  refine ⟨S.max' hS, ?_, ?_⟩
  · have hm : σ (S.max' hS) ≠ S.max' hS := (Finset.mem_filter.mp (S.max'_mem hS)).2
    rcases lt_or_gt_of_ne hm with h | h
    · exact h
    · exfalso
      have hfix : σ (σ (S.max' hS)) = σ (S.max' hS) := by
        by_contra hc
        have : σ (S.max' hS) ∈ S := by simp [S, hc]
        exact absurd (S.le_max' _ this) (not_le.mpr h)
      exact hm (σ.injective hfix)
  · intro j hj
    by_contra hc
    have : j ∈ S := by simp [S, hc]
    exact absurd (S.le_max' _ this) (not_le.mpr hj)
end Formalism.CohomologicalDescent.HeightDescentMinors
