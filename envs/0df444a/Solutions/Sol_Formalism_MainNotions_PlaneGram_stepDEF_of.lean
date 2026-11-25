-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.stepDEF_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:30:09.606157+00:00
-- url     : https://prove2.me/submissions/248afb63-106c-48d8-b628-3da182c312bd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
import Theorems.Thm_Formalism_MainNotions_PlaneGram_omega_value
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digOK_exists
import Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_of_vBB_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_omega_clauses


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (h1 : 1 ≤ C0) (hDIG : DIG K v p) (hG : StepG K v p) (hP : StepP K v p C0)
    (hE : StepE K v p) : StepDEF K v p C0 := by
  intro hD D hV hH _ F hF hF0
  have hF0' := (exists_of_vBB_zero v F hF0).2
  obtain ⟨Pj, hP1, hP2, hP3, hP4, hP5⟩ := hP hD D hV
  obtain ⟨cst, gam, hdig⟩ := D.digOK_exists hDIG hD hV.2.2.1
  obtain ⟨gp, gm, hgp, hgm, happ, hcost⟩ := hG hD D hV cst gam hdig
  obtain ⟨hN, hI, hGd, hch, hY⟩ :=
    omega_clauses hD h1 D hV Pj ⟨hP1, hP2, hP3, hP4, hP5⟩ gp gm hgp hgm hcost
  refine ⟨(dg gm).comp (Pj.comp (dg gp)), ⌈D.Dm p C0 + D.kapD p / 2⌉₊, hN, hI, hGd, hch, hY, ?_⟩
  intro Z hZi hZg
  exact omega_value hD h1 D hV hH hE hF hF0' hdig Pj hP1 hP2 hP4 gp gm hgp happ Z hZi hZg
end Formalism.MainNotions.PlaneGram
