-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3Edges_subset_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:00.608941+00:00
-- url     : https://prove2.me/submissions/b980bda3-5e15-44b3-9c0e-3e3af03eda1a

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11K3Edges G D hCan hmax ⊆
      (paper11K3Supports G D).product
        (paper11K3RightVertices G D hCan hmax) := by
  classical
  intro e he
  obtain ⟨w, hw, u, hu, heq⟩ := by
    simpa [paper11K3Edges] using Finset.mem_biUnion.mp he
  subst e
  have hwInfo := mem_paper11K3Supports G hw
  have hlegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u hu
  have hInc : w ∈ paper11K3IncidentSupports G D hCan hmax u := by
    simp [paper11K3IncidentSupports, hw, hu]
  have huR : u ∈ paper11K3RightVertices G D hCan hmax := by
    rw [paper11K3RightVertices]
    simp only [Finset.mem_filter]
    exact ⟨hlegal.1, ⟨w, hInc⟩⟩
  exact Finset.mem_product.mpr ⟨hw, huR⟩
end C6BipartiteDomination
