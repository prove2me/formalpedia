-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.admissible_at_of_admissible_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:36.141721+00:00
-- url     : https://prove2.me/submissions/d1fa126d-fe10-4a9c-8e5f-84f32887ecbd

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pairwise_iff_idx

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) (L : List C.Letter)
    (hL : AdmList S v L) (hlen : L.length ≤ S.Ntop) : D.AdmAt S v L := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  obtain ⟨⟨h1, h2⟩, hc⟩ := w.2
  refine ⟨⟨Function.update w.1 v L, ⟨⟨fun u => ?_, fun u => ?_⟩, ?_⟩⟩, by simp⟩
  · by_cases hu : u = v
    · subst hu
      generalize hM : Function.update w.1 u L u = M
      have hML : M = L := by rw [← hM]; simp
      subst hML
      exact hL1
    · generalize hM : Function.update w.1 v L u = M
      have hML : M = w.1 u := by rw [← hM]; simp [hu]
      subst hML
      exact h1 u
  · by_cases hu : u = v
    · subst hu
      generalize hM : Function.update w.1 u L u = M
      have hML : M = L := by rw [← hM]; simp
      subst hML
      exact fun j j' hj hj' hne δ hδ1 hδ2 => (pairwise_iff_idx M).1 hL2 j j' hj hj' hne δ hδ1 hδ2
    · generalize hM : Function.update w.1 v L u = M
      have hML : M = w.1 u := by rw [← hM]; simp [hu]
      subst hML
      exact h2 u
  · unfold C.Word.cnt
    refine Finset.sup_le fun u _ => ?_
    by_cases hu : u = v
    · subst hu
      simpa using hlen
    · have hM : Function.update w.1 v L u = w.1 u := by simp [hu]
      rw [hM]
      exact (Finset.le_sup (f := fun u => (w.1 u).length) (Finset.mem_univ u)).trans hc
end Formalism.FourierDecayAlt.P.PBD
