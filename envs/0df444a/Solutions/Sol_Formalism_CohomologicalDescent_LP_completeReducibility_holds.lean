-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.completeReducibility_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:58.609998+00:00
-- url     : https://prove2.me/submissions/90ca1d82-b125-4690-b72a-92c4f1aac877

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds
import Theorems.Thm_Formalism_CohomologicalDescent_LP_existsHighestWeight_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution : CompleteRed := by
  intro K N q _ _ _ _ _ _ T B hU S S' hS hS' hhw
  classical
  have hrefl : B.IsRefl := by
    intro x y h
    exact (hU.symm y x).trans h
  have hRst : Stab T (S ⊓ S') := fun a b x hx =>
    Submodule.mem_inf.mpr ⟨hS a b x (Submodule.mem_inf.mp hx).1, hS' a b x (Submodule.mem_inf.mp hx).2⟩
  have hUst : Stab T (S ⊓ B.orthogonal (S ⊓ S')) := by
    intro a b x hx
    obtain ⟨hxS, hxO⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hS a b x hxS, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hU.symm, hU.adj, hU.symm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) _ (hRst b a n hn)
  have hUbot : S ⊓ B.orthogonal (S ⊓ S') = ⊥ := by
    by_contra hne
    obtain ⟨v, hvU, hv0, μ, hμ⟩ := existsHighestWeight_holds K N q T hU.gl hU.diag _ hUst hne
    obtain ⟨hvS, hvO⟩ := Submodule.mem_inf.mp hvU
    have hvS' := hhw v hvS μ hμ
    have hvv := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvO) v (Submodule.mem_inf.mpr ⟨hvS, hvS'⟩)
    exact (hU.pos v hv0).ne' hvv
  have hcompl : IsCompl (S ⊓ S') (B.orthogonal (S ⊓ S')) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr
      (Submodule.disjoint_def.mpr fun x hxR hxO =>
        Classical.byContradiction fun h =>
          (hU.pos x h).ne' ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) x hxR))
  intro x hxS
  have hx : x ∈ (S ⊓ S') ⊔ B.orthogonal (S ⊓ S') := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hyR, z, hzO, hyz⟩ := Submodule.mem_sup.mp hx
  have hzS : z ∈ S := by
    have hz : z = x - y := by
      rw [← hyz]
      abel
    rw [hz]
    exact S.sub_mem hxS (Submodule.mem_inf.mp hyR).1
  have hz0 : z = 0 := by
    have hzU : z ∈ S ⊓ B.orthogonal (S ⊓ S') := Submodule.mem_inf.mpr ⟨hzS, hzO⟩
    rw [hUbot] at hzU
    exact (Submodule.mem_bot K).mp hzU
  rw [← hyz, hz0, add_zero]
  exact (Submodule.mem_inf.mp hyR).2
end Formalism.CohomologicalDescent.LP
