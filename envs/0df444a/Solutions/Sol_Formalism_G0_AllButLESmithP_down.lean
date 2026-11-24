-- Prove2me | solution 1 for Formalism.G0.AllButLESmithP.down
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:21.851804+00:00
-- url     : https://prove2.me/submissions/3808d7bf-bf8e-4ad4-9365-5d3d4cac8929

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open Formalism.G0.AllButLESmithP
variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]
variable {P : Submodule O M} {n : ℕ}
namespace Formalism.G0.AllButLESmithP
theorem _root_.solution (snf : Basis.SmithNormalForm P ι n) (π : O) (g E : ℕ) (S : Finset ι)
    (hS : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E) (hcard : S.card ≤ g) :
    AllButLE π ⊤ P g E := by
  classical
  refine ⟨S.image snf.bM, by simp, Finset.card_image_le.trans hcard, ?_⟩
  intro x _
  rw [← snf.bM.sum_repr x, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : j ∈ S
  · apply Submodule.mem_sup_right
    rw [smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hj)))
  · obtain ⟨i, rfl, t, ht⟩ := hS j hj
    apply Submodule.mem_sup_left
    have : π ^ E • (snf.bM.repr x (snf.f i) • snf.bM (snf.f i)) =
        (snf.bM.repr x (snf.f i) * t) • (snf.bN i : M) := by
      rw [snf.snf i, smul_smul, smul_smul, ht]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (snf.bN i).2
end Formalism.G0.AllButLESmithP
