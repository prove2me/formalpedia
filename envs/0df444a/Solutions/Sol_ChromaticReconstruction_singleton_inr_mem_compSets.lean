-- Prove2me | solution 1 for ChromaticReconstruction.singleton_inr_mem_compSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:40.893899+00:00
-- url     : https://prove2.me/submissions/a10fdeb8-c14c-452b-b5a3-e8ab5998cf5a

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_leafExt_inr
import Theorems.Thm_ChromaticReconstruction_singleton_mem_compSets_iff


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution {A : Finset (Sym2 (K ⊕ Σ i, Fin (m i)))}
    (hA : A ⊆ (leafExt S m).edgeFinset) {l : Σ i, Fin (m i)} (hl : leafEdge m l ∉ A) :
    {.inr l} ∈ compSets (A : Set (Sym2 (K ⊕ Σ i, Fin (m i)))) := by
  rw [singleton_mem_compSets_iff]
  intro w hw
  have hE := hA hw
  rw [SimpleGraph.mem_edgeFinset] at hE
  have := mem_edgeSet_leafExt_inr hE
  subst this
  exact absurd (by rw [leafEdge, Sym2.eq_swap]; exact hw) hl
end ChromaticReconstruction
