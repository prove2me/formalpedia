-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.nodeOf_mem_grid_or_grid1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:11.241572+00:00
-- url     : https://prove2.me/submissions/cde89612-cd3f-4d1f-b963-3ac2d7632c3d

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (ha : AdmList S v a) (z : C.Letter)
    (hz : z ∈ a) : (∃ n, n ≤ a.length ∧ nodeOf z ∈ S.grid v n) ∨ nodeOf z ∈ S.grid1 v := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  rcases Finset.mem_union.1 (ha.1 j hj) with h | h
  · exact Or.inl ⟨a.length - j, Nat.sub_le _ _, h⟩
  · exact Or.inr h
end Formalism.FourierDecayAlt.P.PBD
