-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.ql_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:55.343396+00:00
-- url     : https://prove2.me/submissions/932f10f2-5593-46ce-b126-39fa02e91bd3

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_ql_map_le

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
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution (r : O) (M Mgg NK : Submodule O V) {n : ℕ} (th : Fin n → V) (h1 : Mgg ≤ M)
    (h2 : Mgg ≤ NK) :
    ql (M.map (r • (LinearMap.id : V →ₗ[O] V)))
        ((M.map (r • (LinearMap.id : V →ₗ[O] V)) ⊓ NK) ⊔
          Submodule.span O (Set.range fun j => r • th j)) ≤
      ql M (Mgg ⊔ Submodule.span O (Set.range th)) := by
  refine ql_map_le _ _ _ _ ?_
  rw [Submodule.map_sup]
  refine sup_le_sup ?_ ?_
  · refine le_inf (Submodule.map_mono h1) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact NK.smul_mem r (h2 hx)
  · rw [Submodule.map_span, ← Set.range_comp]
    exact le_of_eq rfl
end Formalism.MainNotions.Gaps.T0
