-- Prove2me | solution 1 for ChromaticReconstruction.phi_leafExt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:30:45.301878+00:00
-- url     : https://prove2.me/submissions/c70ab8e9-e66b-4717-8a83-ce44e1eff0df

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_phiTerm_inl_eq_zero
import Theorems.Thm_ChromaticReconstruction_extEdges_subset
import Theorems.Thm_ChromaticReconstruction_extEdges_injective
import Theorems.Thm_ChromaticReconstruction_phiTerm_extEdges
import Theorems.Thm_ChromaticReconstruction_phiTerm_inr_eq_zero
import Theorems.Thm_ChromaticReconstruction_phi_eq_sum_phiTerm


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) :
    phi (leafExt S m) = ∑ l0 : Σ i, Fin (m i), ∑ F ∈ S.edgeFinset.powerset,
      (-1) ^ ((∑ i, m i) - 1 + F.card) * killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0)) := by
  rw [phi_eq_sum_phiTerm, sum_comm, Fintype.sum_sum_type]
  rw [sum_eq_zero (fun i _ => sum_eq_zero fun A hA => phiTerm_inl_eq_zero hm
    (mem_powerset.1 hA) i), zero_add]
  refine sum_congr rfl fun l0 _ => ?_
  have hsub : S.edgeFinset.powerset.image (extEdges m l0) ⊆ (leafExt S m).edgeFinset.powerset := by
    intro A hA
    obtain ⟨F, hF, rfl⟩ := mem_image.1 hA
    exact mem_powerset.2 (extEdges_subset (mem_powerset.1 hF))
  rw [← sum_subset hsub (fun A hA hA' => phiTerm_inr_eq_zero (mem_powerset.1 hA) l0 hA'),
    sum_image (fun F _ F' _ h => extEdges_injective l0 h)]
  exact sum_congr rfl fun F _ => phiTerm_extEdges l0 F
end ChromaticReconstruction
