-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d04f8d8d-65e7-5806-87c6-1ff182e127da

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
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra (PadicInt p) B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F)
    (hγ : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ) :
    X.IsHomogeneousVBasis j γ := by
  classical
  refine ⟨fun i => (CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff X j hc i (γ i)).mp (hγ.1 i), ?_⟩

  obtain ⟨-, hsurj, -, -⟩ :=
    MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt p X.F
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
  intro v
  obtain ⟨f, hf⟩ := hsurj v
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 f
  refine ⟨c, ?_⟩
  show Matrix.vecMul c _ = v
  have key := congrArg MvFormalGroup.CartierModule.tangent hcy
  rw [hf] at key
  rw [key]
  erw [map_add, map_sum, CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply,
    MvFormalGroup.CartierModule.tangent_verschiebungInt, add_zero]
  funext k
  simp only [Finset.sum_apply, Matrix.vecMul, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_smul, MvFormalGroup.CartierModule.tangent_smul_witt,
    WittVector.teichmuller_coeff_zero, Pi.smul_apply, smul_eq_mul]

end S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt (solution)
