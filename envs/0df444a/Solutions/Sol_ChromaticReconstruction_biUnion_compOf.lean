-- Prove2me | solution 1 for ChromaticReconstruction.biUnion_compOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:51.541792+00:00
-- url     : https://prove2.me/submissions/f1e1775e-a7ed-432d-9839-029624b93bc0

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_compOf_eq_iff
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_compOf_self
import Theorems.Thm_ChromaticReconstruction_reachable_mono
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A B : Set (Sym2 V)} (hAB : A ⊆ B) (x : V) :
    (compOf A x).biUnion (compOf B) = compOf B x := by
  ext z
  simp only [mem_biUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    have : compOf B y = compOf B x :=
      (compOf_eq_iff.2 (reachable_mono hAB (by simpa [compOf] using hy))).symm
    rwa [← this]
  · intro hz; exact ⟨x, mem_compOf_self A x, hz⟩
end ChromaticReconstruction
