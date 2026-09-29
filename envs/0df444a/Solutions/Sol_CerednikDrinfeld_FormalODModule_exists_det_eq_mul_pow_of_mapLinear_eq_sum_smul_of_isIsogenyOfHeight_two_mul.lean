-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/66be8069-c278-5b58-86b3-19b90cf4b70a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
import Theorems.Thm_Module_length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin
import Theorems.Thm_WittVector_exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y Z : FormalODModule p K) (hY : Y.IsSpecial j) (hZ : Z.IsSpecial j)
    (hY4 : Y.HasHeight 4) (hZ4 : Z.HasHeight 4)
    (hcY : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (hcZ : IsCompl (Z.gradedPiece j 0) (Z.gradedPiece j 1))
    (ρ : SpecialFormal.Series K) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ (2 * h))
    (c : ℤ_[p] →+* WittVector p K)
    (e : Fin 2 → MvFormalGroup.CartierModule p Y.F)
    (he : ∀ m ∈ Y.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r)
    (he0 : ∀ r, e r ∈ Y.gradedPiece j 0)
    (e' : Fin 2 → MvFormalGroup.CartierModule p Z.F)
    (he' : ∀ m ∈ Z.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e' r)
    (he'0 : ∀ r, e' r ∈ Z.gradedPiece j 0)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ r, MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom (e r) = ∑ s, c (A s r) • e' s) :
    ∃ u : ℤ_[p]ˣ, A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h := by
  classical

  have hL :=
    CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
      p K j Y Z hY hZ hY4 hZ4 hcY hcZ ρ h hρ 0
  obtain ⟨-, -, hlen⟩ := hL
  have h0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  rw [h0] at hlen
  set f := MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom

  have he'0' : ∀ r, e' r ∈ Z.gradedSubmodule j 0 := fun r =>
    (FormalODModule.mem_gradedSubmodule_iff _ _ _ _).2 (he'0 r)
  have he'' : ∀ m ∈ Z.gradedSubmodule j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e' r :=
    fun m hm => he' m ((FormalODModule.mem_gradedSubmodule_iff _ _ _ _).1 hm)
  have hc :=
    Module.length_quotient_comap_span_columns_eq_length_quotient_range_mulVecLin
      (WittVector p K) (MvFormalGroup.CartierModule p Z.F) (Z.gradedSubmodule j 0) e' he'0' he'' (A.map c)

  have hspanY : Submodule.span (WittVector p K) (Set.range e) = Y.gradedSubmodule j 0 := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact (FormalODModule.mem_gradedSubmodule_iff _ _ _ _).2 (he0 r)
    · intro m hm
      obtain ⟨w, hw, -⟩ := he m ((FormalODModule.mem_gradedSubmodule_iff _ _ _ _).1 hm)
      rw [hw]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

  have hcols : (fun s : Fin 2 => ∑ r, A.map c r s • e' r) = fun s => f (e s) := by
    funext s
    rw [hA s]
    rfl
  have hspan : Submodule.span (WittVector p K) (Set.range fun s : Fin 2 => ∑ r, A.map c r s • e' r)
      = Submodule.map f (Y.gradedSubmodule j 0) := by
    rw [hcols, ← hspanY, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hspan] at hc

  have hW : Module.length (WittVector p K)
      ((Fin 2 → WittVector p K) ⧸ LinearMap.range (Matrix.mulVecLin (A.map c))) = h :=
    hc.symm.trans hlen
  exact (WittVector.exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq p K c A h).2 hW

end S_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul (solution)
