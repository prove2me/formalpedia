-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.locProb_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:31.599388+00:00
-- url     : https://prove2.me/submissions/0d2af241-8114-4d92-ba05-706199ae20f3

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_thGrid_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_thGrid_sum

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (n' : ℕ) {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (mk : List ℝ → List C.Letter)
    (hmk : ∀ j : Fin K → Fin (d + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (j b))) ∧
      (mk (List.ofFn fun b => grid b (j b))).length ≤ n') :
    KB.LocProb S v n' (pushU grid mk) (pushTh grid mk) := by
  classical
  refine ⟨⟨fun a => ?_, fun a ha => ?_, ?_⟩, fun a ha => ?_⟩
  · unfold pushTh
    exact Finset.sum_nonneg fun j _ => by
      split_ifs
      exacts [thGrid_nonneg grid j, le_refl 0]
  · unfold pushTh
    refine Finset.sum_eq_zero fun j _ => if_neg fun h => ha ?_
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  · unfold pushTh
    rw [Finset.sum_comm, ← thGrid_sum grid hinj]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq, if_pos (by unfold pushU; exact Finset.mem_image_of_mem _ (Finset.mem_univ j))]
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact hmk j
end Formalism.FourierDecayAlt.P.PBD
