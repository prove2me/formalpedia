-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.localStepClosedQDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:35:42.838934+00:00
-- url     : https://prove2.me/submissions/9d8d574c-c200-4ee2-a824-91b5669f491f

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_ql_span_le
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_localStepClosedQDescUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution : LocalStepClosedQDesc := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O O' K K' V V₁ W
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ'
    M Θ Mgg N₁ Z Zm N' e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6
  let jj : V →ₛₗ[algebraMap O O'] V₁ :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a x => by
        show j (a • x) = algebraMap O O' a • j x
        rw [← algebraMap_smul K a x, j.map_smul, ← algebraMap_smul K' (algebraMap O K a) (j x),
          ← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K',
          algebraMap_smul] }
  have hlen : ql (Submodule.span O' (j '' (M : Set V)))
      (Submodule.span O' (j '' (Mgg : Set V)) ⊔ Submodule.span O' (Set.range fun i => j (th i))) ≤
      ql M (Mgg ⊔ Submodule.span O (Set.range th)) := by
    refine ql_span_le ϖ hϖ hϖ' jj M _ _ ?_
    have hle : Mgg ⊔ Submodule.span O (Set.range th) ≤
        (Submodule.span O' (j '' (Mgg : Set V)) ⊔
          Submodule.span O' (Set.range fun i => j (th i))).comap jj := by
      refine sup_le (fun x hx => ?_) (Submodule.span_le.2 ?_)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rintro _ ⟨i, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  refine localStepClosedQDescUp ι ep f ν v νs c' T R I hep hT hc' hv hν O O' K K' V V₁ W j hj ϖ hϖ hϖ'
    M Θ N₁ Z Zm N' (Submodule.span O' (j '' (Mgg : Set V))) e n q (fun i => j (th i)) AA AA' N₁' ρ
    hM hΘ h1 (fun i => Submodule.subset_span ⟨th i, h2 i, rfl⟩)
    (fun i => Submodule.subset_span ⟨th i, h3 i, rfl⟩)
    (Submodule.span_mono (Set.image_mono h4)) ?_ (hlen.trans h6)
  rw [Submodule.span_le]
  have hle : Submodule.span O' (j '' (Mgg : Set V)) ≤
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h5 x hx
  exact fun x hx => hle hx
end Formalism.MainNotions.Gaps.T0
