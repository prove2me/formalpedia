-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.grid1_point_far_from_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:46.921472+00:00
-- url     : https://prove2.me/submissions/c5daae76-4c53-4096-922e-bd6fccf3a5c2

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pt_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_nodeOf_mem_grid_or_grid1
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_four_lt_sq

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : AdmList S v a) {y : ℝ} (hy : y ∈ S.grid1 v) (hyn : y ∉ a.map nodeOf) (z : C.Letter) (hz : z ∈ a)
    {e : ℝ} (he : e ∈ ({0, 1} : Finset ℝ)) : 4 < |(y + e) - z.2| := by
  have hz' := (pt_split z).1
  have he' := (pt_split z).2
  rcases nodeOf_mem_grid_or_grid1 S v a ha z hz with ⟨n, hn, hnode⟩ | hnode
  · have h := (hG v).2.2.2.2.1 y hy n (nodeOf z) hnode e he _ he'
    rw [hz']
    linarith [(four_lt_sq S).2]
  · have hne : y ≠ nodeOf z := fun h => hyn (by rw [h]; exact List.mem_map.2 ⟨z, hz, rfl⟩)
    have h := (hG v).2.2.2.1 y hy (nodeOf z) hnode hne e he _ he'
    rw [hz']
    linarith [(four_lt_sq S).1]
end Formalism.FourierDecayAlt.P.PBD
