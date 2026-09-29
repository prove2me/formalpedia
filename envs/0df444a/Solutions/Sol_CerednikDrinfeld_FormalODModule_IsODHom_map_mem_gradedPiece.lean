-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c8e03304-7d2b-590f-98bc-de3b0c43b694

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X Y : CerednikDrinfeld.FormalODModule p B) (φ : CerednikDrinfeld.SpecialFormal.Series B)
    (hφ : CerednikDrinfeld.FormalODModule.IsODHom X Y φ) (n : ℕ)
    (m : MvFormalGroup.CartierModule p X.F) (hm : m ∈ X.gradedPiece j n) :
    MvFormalGroup.CartierModule.map hφ.1.toHom m ∈ Y.gradedPiece j n := by
  rw [CerednikDrinfeld.FormalODModule.mem_gradedPiece_iff] at hm ⊢
  intro c
  rw [endAct_apply, ← map_comp]
  have hcomm : (Y.actEnd (WittVector.teichmuller p c)).comp hφ.1.toHom =
      hφ.1.toHom.comp (X.actEnd (WittVector.teichmuller p c)) := by
    apply MvFormalGroup.Hom.ext
    exact (hφ.2.1 (WittVector.teichmuller p c)).symm
  rw [hcomm, map_comp, ← endAct_apply (X.actEnd _), hm c, map_homothety]

end S_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece (solution)
