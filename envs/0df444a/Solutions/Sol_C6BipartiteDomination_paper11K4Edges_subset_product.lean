-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4Edges_subset_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:44.281257+00:00
-- url     : https://prove2.me/submissions/94f4f861-6ad8-4b53-996a-789a83c1d596

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11K4Edges G D hCan hmax ⊆
      (paper11K4Supports G D).product
        (paper11K4RightVertices G D hCan hmax) := by
  classical
  intro e he
  obtain ⟨w, hw, u, hu, heq⟩ := by
    simpa [paper11K4Edges] using Finset.mem_biUnion.mp he
  subst e
  have hwInfo := mem_paper11K4Supports G hw
  have hlegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u hu
  have hInc : w ∈ paper11K4IncidentSupports G D hCan hmax u := by
    simp [paper11K4IncidentSupports, hw, hu]
  have huR : u ∈ paper11K4RightVertices G D hCan hmax := by
    rw [paper11K4RightVertices]
    simp only [Finset.mem_filter]
    exact ⟨hlegal.1, ⟨w, hInc⟩⟩
  exact Finset.mem_product.mpr ⟨hw, huR⟩
end C6BipartiteDomination
