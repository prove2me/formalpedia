-- Prove2me | solution 1 for ChromaticReconstruction.nonempty_of_mem_compSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:07:13.710423+00:00
-- url     : https://prove2.me/submissions/df9e9685-d9cc-4897-ae60-47a55dc20649

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {C : Finset V} (hC : C ∈ compSets A) :
    C.Nonempty := by
  simp only [compSets, mem_image, mem_univ, true_and] at hC
  obtain ⟨v, rfl⟩ := hC
  exact ⟨v, by simp⟩
end ChromaticReconstruction
