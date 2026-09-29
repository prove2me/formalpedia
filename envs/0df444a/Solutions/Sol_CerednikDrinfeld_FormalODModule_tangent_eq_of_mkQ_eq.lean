-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.tangent_eq_of_mkQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0b3d7c69-a955-57c6-ab22-59beb75ecc8e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (m m' : MvFormalGroup.CartierModule p X.F)
    (h : (X.toGradedCartierModuleData j hc).vRange.mkQ m = (X.toGradedCartierModuleData j hc).vRange.mkQ m') :
    MvFormalGroup.CartierModule.tangent m = MvFormalGroup.CartierModule.tangent m' := by

  have hmem : m - m' ∈ (X.toGradedCartierModuleData j hc).vRange := (Submodule.Quotient.eq _).mp h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData j hc).mem_vRange_iff _).mp hmem
  have hV : MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.verschiebungInt y) = 0 :=
    MvFormalGroup.CartierModule.tangent_verschiebungInt y
  have hy' : MvFormalGroup.CartierModule.verschiebungInt y = m - m' := by
    rw [← CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply X j hc y]; exact hy
  rw [hy', map_sub, sub_eq_zero] at hV
  exact hV

end S_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq (solution)
