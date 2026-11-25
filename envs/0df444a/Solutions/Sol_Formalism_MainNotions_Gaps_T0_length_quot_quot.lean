-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.length_quot_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:36.111899+00:00
-- url     : https://prove2.me/submissions/8a826784-d262-4f3b-bbb8-ad65ce374eac

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear

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
theorem _root_.solution {O V : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (M Mgg : Submodule O V) {n : ℕ} (th : Fin n → V) (h1 : Mgg ≤ M) (h2 : ∀ j, th j ∈ M) :
    Module.length O ((↥M ⧸ Mgg.comap M.subtype) ⧸ Submodule.span O (Set.range fun j =>
        (Submodule.Quotient.mk ⟨th j, h2 j⟩ : ↥M ⧸ Mgg.comap M.subtype))) =
      Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) := by
  set S : Submodule O ↥M := Mgg.comap M.subtype with hS
  set T : Submodule O ↥M := Submodule.span O (Set.range fun j => (⟨th j, h2 j⟩ : ↥M)) with hT
  have e1 : Submodule.span O (Set.range fun j => (Submodule.Quotient.mk ⟨th j, h2 j⟩ : ↥M ⧸ S)) =
      T.map S.mkQ := by
    rw [hT, Submodule.map_span, ← Set.range_comp]
    rfl
  have hth : Submodule.span O (Set.range th) ≤ M := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h2 j)
  have e2 : (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype = S ⊔ T := by
    apply Submodule.map_injective_of_injective M.injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_sup, hS, Submodule.map_comap_subtype, hT,
      Submodule.map_span, ← Set.range_comp, inf_eq_right.2 (sup_le h1 hth), inf_eq_right.2 h1]
    rfl
  rw [e1, e2]
  exact (Submodule.quotientQuotientEquivQuotientSup S T).length_eq
end Formalism.MainNotions.Gaps.T0
