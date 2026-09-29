-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8ec7a6ff-d1a2-5b05-b7e0-ee49f7957c80

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants

set_option autoImplicit false

universe u

open scoped Matrix in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (a : ℕ → Fin 2 → B)
    (ha : X.HasStructureConstants γ a) (i : Fin 2) :
    MvFormalGroup.linearPart X.varpi *ᵥ MvFormalGroup.CartierModule.tangent (γ i) =
      a 0 i • MvFormalGroup.CartierModule.tangent (γ (CerednikDrinfeld.FormalODModule.piIndex 0 i)) := by
  obtain ⟨h, hh⟩ := ha i 1
  have ht := congrArg MvFormalGroup.CartierModule.tangent hh
  rw [MvFormalGroup.CartierModule.endAct_apply, MvFormalGroup.CartierModule.tangent_map,
    CerednikDrinfeld.FormalODModule.varpiEnd_toPowerSeries] at ht
  rw [ht]
  simp only [Fin.sum_univ_one, Fin.val_zero, Function.iterate_zero, id_eq, Function.iterate_one, map_add,
    MvFormalGroup.CartierModule.tangent_homothety, MvFormalGroup.CartierModule.tangent_verschiebungInt, add_zero]

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants (solution)
