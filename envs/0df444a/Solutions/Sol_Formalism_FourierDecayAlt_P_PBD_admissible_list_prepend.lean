-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.admissible_list_prepend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:16.89531+00:00
-- url     : https://prove2.me/submissions/3c5f19f6-2603-4599-99f9-17e4461ab7e5

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (pre a : List C.Letter) (ha : AdmList S v a)
    (hpre : ∀ j (hj : j < pre.length), nodeOf (pre[j]'hj) ∈ S.grid v (pre.length + a.length - j) ∪ S.grid1 v)
    (hpp : pre.Pairwise Sep) (hpa : ∀ x ∈ pre, ∀ y ∈ a, Sep x y) : AdmList S v (pre ++ a) := by
  refine ⟨fun j hj => ?_, List.pairwise_append.2 ⟨hpp, ha.2, hpa⟩⟩
  by_cases hjp : j < pre.length
  · rw [List.getElem_append_left hjp, List.length_append]
    exact hpre j hjp
  · have hj2 : j - pre.length < a.length := by
      rw [List.length_append] at hj
      omega
    rw [List.getElem_append_right (by omega), List.length_append,
      show pre.length + a.length - j = a.length - (j - pre.length) by omega]
    exact ha.1 (j - pre.length) hj2
end Formalism.FourierDecayAlt.P.PBD
