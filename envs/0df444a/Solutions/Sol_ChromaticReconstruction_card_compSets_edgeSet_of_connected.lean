-- Prove2me | solution 1 for ChromaticReconstruction.card_compSets_edgeSet_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:27:39.288218+00:00
-- url     : https://prove2.me/submissions/4db604f0-7193-4226-9d31-e0f8a3d4ec10

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_compSets_eq_image_compOf
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} (hG : G.Connected) :
    (compSets G.edgeSet).card = 1 := by
  rw [card_eq_one]
  obtain ⟨v⟩ := hG.nonempty
  refine ⟨univ, ?_⟩
  rw [compSets_eq_image_compOf]
  have : ∀ x, compOf G.edgeSet x = univ := by
    intro x
    ext y
    simp only [compOf, mem_filter, mem_univ, true_and, iff_true, SimpleGraph.fromEdgeSet_edgeSet]
    exact hG.preconnected x y
  rw [show compOf G.edgeSet = fun _ => univ from funext this]
  exact image_const ⟨v, mem_univ v⟩ univ
end ChromaticReconstruction
