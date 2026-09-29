-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/cad82a2c-d5f5-5921-914e-272dc5994044

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic
import Theorems.Thm_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

noncomputable section

namespace K82Edge

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

section Transport

variable {R S : Type} [CommRing R] [CommRing S]

theorem hasStructureConstants_map_edgeConstants (φ : R →+* S) (Y : FormalODModule p R)
    (δ : Fin 2 → CartierModule p Y.F) (ξ η : R)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    (Y.map φ).HasStructureConstants (fun i => baseChange φ (δ i))
      (EdgeFamily.edgeConstants p (φ ξ) (φ η)) := by
  have h := ha.map φ
  have e : (fun m i => φ (EdgeFamily.edgeConstants p ξ η m i)) =
      EdgeFamily.edgeConstants p (φ ξ) (φ η) := by
    funext m i
    exact EdgeFamily.edgeConstants_map φ ξ η m i
  rw [e] at h
  exact h

theorem isHomogeneousVBasis_map_of_eq (φ : R →+* S) {Y : FormalODModule p R} {j : Zp2 p →+* R}
    {δ : Fin 2 → CartierModule p Y.F} (h : Y.IsHomogeneousVBasis j δ) {j' : Zp2 p →+* S}
    (hj : φ.comp j = j') :
    (Y.map φ).IsHomogeneousVBasis j' fun i => baseChange φ (δ i) := by
  subst hj
  exact h.map φ

end Transport

section Point

variable {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R) (ξ η : R)
  (Y : FormalODModule p R) (δ : Fin 2 → CartierModule p Y.F)

theorem pi_apply_zero (hξη : ξ * η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (δ 0) =
      (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) • δ 1 +
        verschiebungInt (δ 0) :=
  (CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
    p j ξ η hξη Y δ hδ ha).1

theorem pi_apply_one (hξη : ξ * η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (δ 1) =
      (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • δ 0 +
        verschiebungInt (δ 1) :=
  (CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
    p j ξ η hξη Y δ hδ ha).2

omit [CharP R p] in

theorem teichmuller_smul_verschiebungInt_eq (c : R) (f : CartierModule p Y.F) :
    WittVector.teichmuller p c • verschiebungInt f =
      verschiebungInt (WittVector.teichmuller p (c ^ p) • f) := by
  rw [smul_verschiebungInt, WittVector.frobenius_teichmuller_eq]

theorem pi_one_eq_verschiebungInt_of_left_eq_zero (hξ : ξ = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1) := by
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  rw [pi_apply_one j ξ η Y δ hξη hδ ha, hξ, zero_pow (Fact.out : p.Prime).ne_zero,
    WittVector.teichmuller_zero, sub_self, zero_smul, zero_add]

theorem pi_zero_eq_verschiebungInt_of_right_eq_zero (hη : η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0) := by
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  rw [pi_apply_zero j ξ η Y δ hξη hδ ha, hη, zero_pow (Fact.out : p.Prime).ne_zero,
    WittVector.teichmuller_zero, sub_self, zero_smul, zero_add]

theorem pi_eq_verschiebungInt_etaInv (hξ : ξ = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1) =
      verschiebungInt (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1) := by
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  have h0 := pi_apply_zero j ξ η Y δ hξη hδ ha
  have h1 := pi_one_eq_verschiebungInt_of_left_eq_zero j ξ η Y δ hξ hδ ha
  rw [map_sub, endAct_smul_witt, endAct_verschiebungInt, h0, h1,
    teichmuller_smul_verschiebungInt_eq, map_add, sub_smul, map_sub, map_sub]
  abel

theorem pi_eq_verschiebungInt_xiInv (hη : η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0) =
      verschiebungInt (verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0) := by
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  have h1 := pi_apply_one j ξ η Y δ hξη hδ ha
  have h0 := pi_zero_eq_verschiebungInt_of_right_eq_zero j ξ η Y δ hη hδ ha
  rw [map_sub, endAct_smul_witt, endAct_verschiebungInt, h1, h0,
    teichmuller_smul_verschiebungInt_eq, map_add, sub_smul, map_sub, map_sub]
  abel

end Point

section Lie

variable {R : Type} [CommRing R] (Y : FormalODModule p R)

theorem tangent_endAct_varpiEnd (f : CartierModule p Y.F) :
    tangent (endAct Y.varpiEnd f) = Y.lieVarpi (tangent f) := by
  show tangent (CartierModule.map Y.varpiEnd f) = Matrix.mulVecLin (linearPart Y.varpi) (tangent f)
  rw [tangent_map]
  rfl

theorem tangent_teichmuller_sub_smul (a b : R) (f : CartierModule p Y.F) :
    tangent ((WittVector.teichmuller p a - WittVector.teichmuller p b) • f) = (a - b) • tangent f := by
  rw [tangent_smul_witt]
  congr 1
  show WittVector.constantCoeff (WittVector.teichmuller p a - WittVector.teichmuller p b) = a - b
  rw [map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]

variable [CharP R p] (j : Zp2 p →+* R) (ξ η : R) (δ : Fin 2 → CartierModule p Y.F)

theorem lieVarpi_tangent_zero (hξη : ξ * η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    Y.lieVarpi (tangent (δ 0)) = (η ^ p - η) • tangent (δ 1) := by
  rw [← tangent_endAct_varpiEnd, K82Edge.pi_apply_zero j ξ η Y δ hξη hδ ha, map_add,
    tangent_verschiebungInt, add_zero, tangent_teichmuller_sub_smul]

theorem lieVarpi_tangent_one (hξη : ξ * η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    Y.lieVarpi (tangent (δ 1)) = (ξ ^ p - ξ) • tangent (δ 0) := by
  rw [← tangent_endAct_varpiEnd, K82Edge.pi_apply_one j ξ η Y δ hξη hδ ha, map_add,
    tangent_verschiebungInt, add_zero, tangent_teichmuller_sub_smul]

omit [CharP R p] in

theorem exists_eq_smul_tangent_add (hδ : Y.IsHomogeneousVBasis j δ) (v : Y.Lie) :
    ∃ c : Fin 2 → R, v = c 0 • tangent (δ 0) + c 1 • tangent (δ 1) := by
  classical
  obtain ⟨c, key⟩ : ∃ c : Fin 2 → R,
      Matrix.vecMul c (Matrix.of fun i k => tangent (δ i) k) = v := by
    refine ⟨Matrix.vecMul v (Matrix.of fun i k => tangent (δ i) k)⁻¹, ?_⟩
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hδ.2, Matrix.vecMul_one]
  refine ⟨c, ?_⟩
  rw [← key]
  funext k
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.of_apply]

omit [CharP R p] in

theorem exists_eq_smul_tangent_one_of_mem_lieOne (hR : IsNilpotent (p : R))
    (hLie : IsCompl (Y.lieZero j) (Y.lieOne j)) (hδ : Y.IsHomogeneousVBasis j δ)
    (v : Y.Lie) (hv : v ∈ Y.lieOne j) : ∃ c : R, v = c • tangent (δ 1) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_tangent_add Y j δ hδ v
  have ht := CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hR Y
  have h0 : tangent (δ 0) ∈ Y.lieZero j := ht.1 _ (hδ.1 0)
  have h1 : tangent (δ 1) ∈ Y.lieOne j := ht.2 _ (hδ.1 1)
  have hmem0 : c 0 • tangent (δ 0) ∈ Y.lieZero j := Submodule.smul_mem _ _ h0
  have hmem1 : c 0 • tangent (δ 0) ∈ Y.lieOne j := by
    have : c 0 • tangent (δ 0) = v - c 1 • tangent (δ 1) := by rw [hc]; abel
    rw [this]
    exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ h1)
  have hzero : c 0 • tangent (δ 0) = 0 := by
    have hmem : c 0 • tangent (δ 0) ∈ Y.lieZero j ⊓ Y.lieOne j := Submodule.mem_inf.2 ⟨hmem0, hmem1⟩
    rw [hLie.inf_eq_bot] at hmem
    exact (Submodule.mem_bot R).1 hmem
  exact ⟨c 1, by rw [hc, hzero, zero_add]⟩

omit [CharP R p] in

theorem exists_eq_smul_tangent_zero_of_mem_lieZero (hR : IsNilpotent (p : R))
    (hLie : IsCompl (Y.lieZero j) (Y.lieOne j)) (hδ : Y.IsHomogeneousVBasis j δ)
    (v : Y.Lie) (hv : v ∈ Y.lieZero j) : ∃ c : R, v = c • tangent (δ 0) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_tangent_add Y j δ hδ v
  have ht := CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hR Y
  have h0 : tangent (δ 0) ∈ Y.lieZero j := ht.1 _ (hδ.1 0)
  have h1 : tangent (δ 1) ∈ Y.lieOne j := ht.2 _ (hδ.1 1)
  have hmem1 : c 1 • tangent (δ 1) ∈ Y.lieOne j := Submodule.smul_mem _ _ h1
  have hmem0 : c 1 • tangent (δ 1) ∈ Y.lieZero j := by
    have : c 1 • tangent (δ 1) = v - c 0 • tangent (δ 0) := by rw [hc]; abel
    rw [this]
    exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ h0)
  have hzero : c 1 • tangent (δ 1) = 0 := by
    have hmem : c 1 • tangent (δ 1) ∈ Y.lieZero j ⊓ Y.lieOne j := Submodule.mem_inf.2 ⟨hmem0, hmem1⟩
    rw [hLie.inf_eq_bot] at hmem
    exact (Submodule.mem_bot R).1 hmem
  exact ⟨c 0, by rw [hc, hzero, add_zero]⟩

theorem lieOne_le_ker_lieVarpi_of_left_eq_zero (hξ : ξ = 0) (hR : IsNilpotent (p : R))
    (hLie : IsCompl (Y.lieZero j) (Y.lieOne j)) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    Y.lieOne j ≤ LinearMap.ker Y.lieVarpi := by
  intro v hv
  obtain ⟨c, rfl⟩ := exists_eq_smul_tangent_one_of_mem_lieOne Y j δ hR hLie hδ v hv
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  rw [LinearMap.mem_ker, map_smul, lieVarpi_tangent_one Y j ξ η δ hξη hδ ha, hξ,
    zero_pow (Fact.out : p.Prime).ne_zero, sub_self, zero_smul, smul_zero]

theorem exists_mem_lieZero_lieVarpi_eq_of_left_eq_zero (hξ : ξ = 0) (hu : IsUnit (η ^ p - η))
    (hR : IsNilpotent (p : R)) (hLie : IsCompl (Y.lieZero j) (Y.lieOne j))
    (hδ : Y.IsHomogeneousVBasis j δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η))
    (v : Y.Lie) (hv : v ∈ Y.lieOne j) : ∃ u ∈ Y.lieZero j, Y.lieVarpi u = v := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_tangent_one_of_mem_lieOne Y j δ hR hLie hδ v hv
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  obtain ⟨w, hw⟩ := hu
  have h0 : tangent (δ 0) ∈ Y.lieZero j :=
    (CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hR Y).1 _ (hδ.1 0)
  refine ⟨(c * (w⁻¹ : Rˣ)) • tangent (δ 0), Submodule.smul_mem _ _ h0, ?_⟩
  rw [map_smul, lieVarpi_tangent_zero Y j ξ η δ hξη hδ ha, ← hw, smul_smul, mul_assoc,
    Units.inv_mul, mul_one]

theorem lieZero_le_ker_lieVarpi_of_right_eq_zero (hη : η = 0) (hR : IsNilpotent (p : R))
    (hLie : IsCompl (Y.lieZero j) (Y.lieOne j)) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    Y.lieZero j ≤ LinearMap.ker Y.lieVarpi := by
  intro v hv
  obtain ⟨c, rfl⟩ := exists_eq_smul_tangent_zero_of_mem_lieZero Y j δ hR hLie hδ v hv
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  rw [LinearMap.mem_ker, map_smul, lieVarpi_tangent_zero Y j ξ η δ hξη hδ ha, hη,
    zero_pow (Fact.out : p.Prime).ne_zero, sub_self, zero_smul, smul_zero]

theorem exists_mem_lieOne_lieVarpi_eq_of_right_eq_zero (hη : η = 0) (hu : IsUnit (ξ ^ p - ξ))
    (hR : IsNilpotent (p : R)) (hLie : IsCompl (Y.lieZero j) (Y.lieOne j))
    (hδ : Y.IsHomogeneousVBasis j δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η))
    (v : Y.Lie) (hv : v ∈ Y.lieZero j) : ∃ u ∈ Y.lieOne j, Y.lieVarpi u = v := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_tangent_zero_of_mem_lieZero Y j δ hR hLie hδ v hv
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  obtain ⟨w, hw⟩ := hu
  have h1 : tangent (δ 1) ∈ Y.lieOne j :=
    (CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hR Y).2 _ (hδ.1 1)
  refine ⟨(c * (w⁻¹ : Rˣ)) • tangent (δ 1), Submodule.smul_mem _ _ h1, ?_⟩
  rw [map_smul, lieVarpi_tangent_one Y j ξ η δ hξη hδ ha, ← hw, smul_smul, mul_assoc,
    Units.inv_mul, mul_one]

end Lie

end K82Edge

namespace K81

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData

theorem hasDetIndex_stdLattice (p : ℕ) [Fact p.Prime] :
    HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (stdLattice ℤ_[p] ℚ_[p]) 0 := by
  refine ⟨1, latticeMap_one _, 1, ?_⟩
  simp

theorem lattice_of_pi (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (x : PrimeSpectrum B)
    (hPi0 : ∀ s, Q.Pi₀ s = 0) (hPi1 : Function.Surjective Q.Pi₁)
    (hlow : stdLattice ℤ_[p] ℚ_[p] ≤ Q.N₀ x) :
    Q.N₀ x = stdLattice ℤ_[p] ℚ_[p] ∧
      Q.N₁ x = latticeMap (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
        (stdLattice ℤ_[p] ℚ_[p]) := by
  have hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁) := by
    have : LinearMap.range Q.Pi₀ = ⊥ := LinearMap.range_eq_bot.mpr (LinearMap.ext fun s => hPi0 s)
    rw [this]; exact bot_le
  have h0 : Q.N₀ x = stdLattice ℤ_[p] ℚ_[p] :=
    (LT.LatticeTree.eq_of_le_of_hasDetIndex_padic p _ _ hlow 0 (hasDetIndex_stdLattice p)
      (Q.hasDetIndex₀ x hS0)).symm
  have hsurjLoc : Function.Surjective (LocalizedModule.map x.asIdeal.primeCompl Q.Pi₁) :=
    LocalizedModule.map_surjective _ _ hPi1
  have hdiv : ∀ v ∈ Q.N₀ x, ∃ w ∈ Q.N₁ x, v = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w := by
    intro v hv
    obtain ⟨y, hy⟩ := hsurjLoc (Q.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))))
    exact Q.injective₀ x ⟨v, hv⟩
      (Submodule.mem_sup_left ((Submodule.restrictScalars_mem B _ _).2 ⟨y, hy⟩))
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : ((unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) := by
    rw [unitOfNeZero_coe]; simp
  have halg : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) = (p : ℚ_[p]) := by simp
  refine ⟨h0, ?_⟩
  ext v
  rw [mem_latticeMap_scalarGL]
  constructor
  · intro hv
    refine ⟨(p : ℚ_[p]) • v, ?_, ?_⟩
    · rw [← h0, ← halg]; exact Q.smul_le x v hv
    · rw [Units.val_inv_eq_inv_val, hu, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  · rintro ⟨w, hw, rfl⟩
    rw [← h0] at hw
    obtain ⟨w', hw', rfl⟩ := hdiv w hw
    rw [halg, Units.val_inv_eq_inv_val, hu, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    exact hw'

theorem pi_of_T (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (X : FormalODModule p B) (j : Zp2 p →+* B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (τ₀ : Q.T₀ ≃ₗ[B] ↥(X.lieZero j)) (τ₁ : Q.T₁ ≃ₗ[B] ↥(X.lieOne j))
    (hT0 : ∀ s : Q.T₀, ((τ₁ (Q.Pi₀ s) : ↥(X.lieOne j)) : X.Lie) = X.lieVarpi ((τ₀ s : ↥(X.lieZero j)) : X.Lie))
    (hT1 : ∀ s : Q.T₁, ((τ₀ (Q.Pi₁ s) : ↥(X.lieZero j)) : X.Lie) = X.lieVarpi ((τ₁ s : ↥(X.lieOne j)) : X.Lie))
    (hcrit : X.lieZero j ≤ LinearMap.ker X.lieVarpi)
    (hsurj : ∀ v ∈ X.lieZero j, ∃ w ∈ X.lieOne j, X.lieVarpi w = v) :
    (∀ s, Q.Pi₀ s = 0) ∧ Function.Surjective Q.Pi₁ := by
  constructor
  · intro s
    have h1 : ((τ₁ (Q.Pi₀ s) : ↥(X.lieOne j)) : X.Lie) = 0 := by
      rw [hT0]; exact LinearMap.mem_ker.1 (hcrit (τ₀ s).2)
    have h2 : τ₁ (Q.Pi₀ s) = 0 := Subtype.ext h1
    simpa using h2
  · intro t₀
    obtain ⟨w, hw, hwv⟩ := hsurj _ (τ₀ t₀).2
    refine ⟨τ₁.symm ⟨w, hw⟩, ?_⟩
    apply τ₀.injective
    apply Subtype.ext
    rw [hT1, LinearEquiv.apply_symm_apply]
    exact hwv

end K81

namespace K81

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData

theorem isHausdorff_of_isNilpotent {p : ℕ} {S' : Type} [CommRing S'] (hS : IsNilpotent ((p : ℕ) : S')) :
    IsHausdorff (Ideal.span {((p : ℕ) : S')}) S' := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem charP_of_natCast_eq_zero (p : ℕ) [Fact p.Prime] {B : Type} [Field B] (hB : (p : B) = 0) : CharP B p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).mpr hB

theorem charP_away_one (p : ℕ) [Fact p.Prime] {B : Type} [Field B] (hB : (p : B) = 0) :
    CharP (Rigidified.Baway (1 : B)) p :=
  haveI := charP_of_natCast_eq_zero p hB
  charP_of_injective_ringHom (f := (IsLocalization.atOne B (Rigidified.Baway (1 : B))).toRingEquiv.toRingHom)
    (fun a b h => (IsLocalization.atOne B (Rigidified.Baway (1 : B))).toRingEquiv.injective h) p

theorem natCast_away_eq_zero (p : ℕ) {B : Type} [Field B] (hB : (p : B) = 0) :
    (p : Rigidified.Baway (1 : B)) = 0 := by
  rw [← map_natCast (Rigidified.awayHom (1 : B)) p, hB, map_zero]

theorem charP_away_one_quot (p : ℕ) [Fact p.Prime] {B : Type} [Field B] (hB : (p : B) = 0) :
    CharP (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))) p := by
  haveI := charP_away_one p hB
  have hbot : pIdeal p (Rigidified.Baway (1 : B)) = ⊥ := by
    rw [pIdeal, natCast_away_eq_zero p hB, Ideal.span_singleton_eq_bot]
  let e : Rigidified.Baway (1 : B) ≃+* Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B)) :=
    ((Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _)).symm
  exact charP_of_injective_ringHom (f := e.toRingHom) (fun a b h => e.injective h) p

theorem mk_comp_eq_reduceMap_comp_mk {p : ℕ} {B S' : Type} [CommRing B] [CommRing S'] (g : B →+* S') :
    (Ideal.Quotient.mk (pIdeal p S')).comp g = (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B)) := by
  apply RingHom.ext; intro b
  show Ideal.Quotient.mk (pIdeal p S') (g b) = reduceMap g (Ideal.Quotient.mk (pIdeal p B) b)
  rw [reduceMap, residueMap, Ideal.quotientMap_mk]

theorem baseChangeEq_congr {p : ℕ} [Fact p.Prime] {d : ℕ} {R S : Type} [CommRing R] [CommRing S]
    {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} [Φ.IsComm] [Ψ.IsComm]
    (f g : R →+* S) (hfg : f = g) (h : Φ.map f = Ψ) (h' : Φ.map g = Ψ) (m : CartierModule p Φ) :
    baseChangeEq f h m = baseChangeEq g h' m := by
  subst hfg; rfl

theorem endAct_varpiEnd_endAct_varpiEnd {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (m : CartierModule p X.F) :
    endAct X.varpiEnd (endAct X.varpiEnd m) = p • m := by
  have h : endAct X.varpiEnd (endAct X.varpiEnd m) = endAct (X.varpiEnd * X.varpiEnd) m := by
    rw [map_mul]; rfl
  rw [h, X.varpiEnd_mul_varpiEnd, map_natCast X.actRingHom, endAct_natCast]

theorem smul_alg {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (n : ℕ) (a b : R) (g v : M) :
    n • ((a - b) • g + v) - a • (n • g) = n • (v - b • g) := by
  rw [smul_comm a n g, ← smul_sub, sub_smul]
  congr 1
  abel

theorem pow_smul_smul {M : Type} [AddCommMonoid M] (p a m : ℕ) (z : M) :
    p ^ (a + m) • (p • z) = p ^ (a + (m + 1) + 0) • z := by
  rw [smul_smul, ← pow_succ, add_zero, ← add_assoc]

end K81

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in

set_option maxHeartbeats 160000000 in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
(ρ₁ : FormalODModule.Hom ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X)
(hρ₁0 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))
(hρ₁1 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))
(hρ₁h : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁.toSeries 4)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* Ω)
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ≠ 0)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω)
    (hQ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q)
    (x : PrimeSpectrum Ω) :
    Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 ∧
      Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])).1 := by
  classical
  obtain ⟨hOD, τ₀, τ₁, hT0, hT1, H⟩ := hQ

  have hpE : ((p : ℕ) : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    rw [← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _), ← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k)))]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]
  have hp0 : ((p : ℕ) : Ω) = 0 := by rw [← map_natCast y, hpE, map_zero]
  haveI : CharP Ω p := K81.charP_of_natCast_eq_zero p hp0
  have hΩnil : IsNilpotent ((p : ℕ) : Ω) := ⟨1, by rw [pow_one, hp0]⟩

  have hyη : y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    have h := congrArg y (EdgeFamily.edgeRingCharP.ξ_mul_η p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    rw [map_mul, map_zero] at h
    exact (mul_eq_zero.1 h).resolve_left hyξ
  have hunit : IsUnit (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p -
      y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    have hd := (FormalOmega.chartERing.isUnit_discr (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : WittVector p k ⧸ pIdeal p (WittVector p k)) p).map y
    rw [map_mul] at hd
    have h1 := isUnit_of_mul_isUnit_left hd
    rw [map_sub, map_pow, map_one] at h1
    have hne : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ (p - 1) - 1 ≠ 0 := h1.ne_zero
    rw [isUnit_iff_ne_zero]
    have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm
    intro h0
    apply hne
    have : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) *
        (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ (p - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', ← hp1]; exact h0
    exact (mul_eq_zero.1 this).resolve_left hyξ

  have hδ' : (FormalODModule.map y X).IsHomogeneousVBasis
      (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))))
      (fun i => baseChange y (γ i)) :=
    K82Edge.isHomogeneousVBasis_map_of_eq y hγ rfl
  have ha' := K82Edge.hasStructureConstants_map_edgeConstants y X γ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) hγa
  have hLie := (CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent
    p _ hΩnil (FormalODModule.map y X) _ hδ').2.2.2
  have hcrit := K82Edge.lieZero_le_ker_lieVarpi_of_right_eq_zero (FormalODModule.map y X) (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (fun i => baseChange y (γ i)) hyη hΩnil hLie hδ' ha'
  have hsurj := K82Edge.exists_mem_lieOne_lieVarpi_eq_of_right_eq_zero (FormalODModule.map y X) (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (fun i => baseChange y (γ i)) hyη hunit hΩnil hLie hδ' ha'
  obtain ⟨hPi0, hPi1⟩ := K81.pi_of_T p (FormalODModule.map y X) _ Q τ₀ τ₁ hT0 hT1 hcrit hsurj

  have hlow : stdLattice ℤ_[p] ℚ_[p] ≤ Q.N₀ x := by

    obtain ⟨hcS, hcbS, hcΦS⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hΩnil ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (1 : Ω)
    haveI hCS : CharP (Rigidified.Baway (1 : Ω)) p := K81.charP_away_one p hp0
    haveI hCSb : CharP ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω))) p := K81.charP_away_one_quot p hp0
    have hSnil : IsNilpotent ((p : ℕ) : (Rigidified.Baway (1 : Ω))) := ⟨1, by rw [pow_one, K81.natCast_away_eq_zero p hp0]⟩
    have hηS : ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) = 0 := by rw [hyη, map_zero]
    have hηB : ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) = 0 := by rw [hyη, map_zero, map_zero]

    have hδY : (FormalODModule.map y X).IsHomogeneousVBasis (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (fun i => (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))) := hδ'
    have haY : (FormalODModule.map y X).HasStructureConstants (fun i => (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))) (EdgeFamily.edgeConstants p (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) := ha'
    have hδS : (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).IsHomogeneousVBasis (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) :=
      K82Edge.isHomogeneousVBasis_map_of_eq (Rigidified.awayHom (1 : Ω)) hδY rfl
    have haS : (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).HasStructureConstants (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) (EdgeFamily.edgeConstants p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) :=
      K82Edge.hasStructureConstants_map_edgeConstants (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X) (fun i => (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) haY
    have hδM : (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).IsHomogeneousVBasis (((Ideal.Quotient.mk (pIdeal p Ω))).comp (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))))) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) :=
      K82Edge.isHomogeneousVBasis_map_of_eq (Ideal.Quotient.mk (pIdeal p Ω)) hδY rfl
    have haM : (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).HasStructureConstants (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) (EdgeFamily.edgeConstants p ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) :=
      K82Edge.hasStructureConstants_map_edgeConstants (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X) (fun i => (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) haY
    have hδB : (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).IsHomogeneousVBasis (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))))) :=
      K82Edge.isHomogeneousVBasis_map_of_eq (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) hδM rfl
    have haB : (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).HasStructureConstants (fun i => (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))))) (EdgeFamily.edgeConstants p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) :=
      K82Edge.hasStructureConstants_map_edgeConstants (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) haM

    obtain ⟨L, hL⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (K81.isHausdorff_of_isNilpotent hSnil) (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) hδS hcS

    have hcritS := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi p (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (FormalODModule.map y X) hLie hcrit (Rigidified.awayHom (1 : Ω))
    have hi : ∀ m' ∈ (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0, ∃ g' : CartierModule p (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F,
        verschiebungInt g' = endAct (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).varpiEnd m' := by
      rw [verschiebungInt_eq_verschiebung]
      exact hcritS

    have hPiS0 : endAct (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).varpiEnd (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) = verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) :=
      K82Edge.pi_zero_eq_verschiebungInt_of_right_eq_zero (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) hηS hδS haS
    have hPiS1 : endAct (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).varpiEnd (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) = verschiebungInt (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) :=
      K82Edge.pi_eq_verschiebungInt_xiInv (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) hηS hδS haS
    have hm0 : (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) ∈ (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0 := hδS.1 0
    have hmV : verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) ∈ (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0 := by
      have h := CerednikDrinfeld.FormalODModule.verschiebungInt_mem_gradedPiece_succ (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 1 (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) (hδS.1 1)
      have h2 : (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (1 + 1) = (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0 :=
        CerednikDrinfeld.FormalODModule.gradedPiece_add_two (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0
      rw [h2] at h
      exact h
    have hm1 : (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) ∈ (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0 :=
      sub_mem hmV (CerednikDrinfeld.FormalODModule.smul_mem_gradedPiece (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0 _ (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) hm0)
    have hL0 : L (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) = ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))), 0) :=
      CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) hcS L hL 0 hi (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))) hm0 hPiS0.symm
    have hL1 : L (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) = ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))), 0) :=
      CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)) hcS L hL 0 hi (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) hm1 hPiS1.symm

    have hz : ∀ (e : CartierModule p (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F), e ∈ (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).gradedPiece (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) 0 → L e = ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (e, 0) →
        ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (e, 0) ∈ ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).etaPiece L hL.isCartierLMap.map_verschiebung 0 := by
      intro e he hLe
      refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk, hLe]
        simp only [Prod.mk_zero_zero, map_zero, add_zero]
      · exact AddSubgroup.mem_map.2 ⟨(e, 0), AddSubgroup.mem_prod.2
          ⟨(CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcS 0 _).2 he, zero_mem _⟩, rfl⟩

    have hred : ∀ i : Fin 2, Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))) = (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i)))) := by
      intro i
      apply CartierModule.ext
      funext j
      show ((MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω))))).comp (MvPowerSeries.map (Rigidified.awayHom (1 : Ω)))) (MvPowerSeries.map y ((γ i).toPowerSeries j)) =
        ((MvPowerSeries.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω)))).comp (MvPowerSeries.map (Ideal.Quotient.mk (pIdeal p Ω)))) (MvPowerSeries.map y ((γ i).toPowerSeries j))
      rw [← MvPowerSeries.map_comp, ← MvPowerSeries.map_comp, K81.mk_comp_eq_reduceMap_comp_mk]
    have hcc : (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) = ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) :=
      RingHom.congr_fun (K81.mk_comp_eq_reduceMap_comp_mk (p := p) (Rigidified.awayHom (1 : Ω))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))

    have hPiB0 : endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) = verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) :=
      K82Edge.pi_zero_eq_verschiebungInt_of_right_eq_zero (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))))) hηB hδB haB
    have hPiB1 : endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) =
        (WittVector.teichmuller p (((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p) - WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) + verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) :=
      K82Edge.pi_apply_one (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))) (fun i => (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ i))))) (by rw [hηB, mul_zero]) hδB haB

    have hb3V : ∀ z : CartierModule p X.F, (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (verschiebungInt z)))) = verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl z))) := by
      intro z
      rw [baseChangeEq_verschiebungInt y]
      rw [baseChangeEq_verschiebungInt (Ideal.Quotient.mk (pIdeal p Ω))]
      rw [baseChangeEq_verschiebungInt (reduceMap (p := p) (Rigidified.awayHom (1 : Ω)))]
    have hscT : ∀ c : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))), WittVector.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (WittVector.map (Ideal.Quotient.mk (pIdeal p Ω)) (WittVector.map y (WittVector.teichmuller p c))) =
        WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y c))) := by
      intro c
      rw [WittVector.map_teichmuller, WittVector.map_teichmuller, WittVector.map_teichmuller]
    have hb3T : ∀ (c : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (z : CartierModule p X.F),
        (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (WittVector.teichmuller p c • z)))) = WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y c))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl z))) := by
      intro c z
      rw [baseChangeEq_smul_witt y]
      rw [baseChangeEq_smul_witt (Ideal.Quotient.mk (pIdeal p Ω))]
      rw [baseChangeEq_smul_witt (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))), hscT]
    have hscP : WittVector.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (WittVector.map (Ideal.Quotient.mk (pIdeal p Ω)) (WittVector.map y (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) = ((p : ℕ) : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) := by
      rw [map_natCast (WittVector.map y) p, map_natCast (WittVector.map (Ideal.Quotient.mk (pIdeal p Ω))) p, map_natCast (WittVector.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω)))) p]
    have hb3P : ∀ z : CartierModule p X.F, (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl ((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • z)))) = (p : ℕ) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl z))) := by
      intro z
      rw [baseChangeEq_smul_witt y]
      rw [baseChangeEq_smul_witt (Ideal.Quotient.mk (pIdeal p Ω))]
      rw [baseChangeEq_smul_witt (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))), hscP, Nat.cast_smul_eq_nsmul (WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) p]
    have hb3sub : ∀ z z' : CartierModule p X.F, (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (z - z')))) = (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl z))) - (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl z'))) := by
      intro z z'
      rw [map_sub (baseChangeEq (p := p) (Ψ := (FormalODModule.map y X).F) y rfl) z z']
      rw [map_sub (baseChangeEq (p := p) (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl)]
      rw [map_sub (baseChangeEq (p := p) (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl)]

    have hpw0 : (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2))) = 0 := by
      rw [map_pow, map_pow, map_pow, hηB, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    have hpw1 : (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2))) = ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2 := by
      rw [map_pow, map_pow, map_pow]
    have hV0zero : verschiebungInt (WittVector.teichmuller p (0 : ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))))) = 0 := by
      rw [WittVector.teichmuller_zero, zero_smul, map_zero]
    have kB0b : (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))))) = 0 :=
      (hb3V _).trans ((congrArg verschiebungInt ((hb3T _ _).trans
        (congrArg (fun s : ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω))) => WittVector.teichmuller p s • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))))) hpw0))).trans hV0zero)
    have keyB0 : (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1)))))) = (p : ℕ) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) :=
      (hb3sub ((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0) (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))).trans ((congr (congrArg (· - ·) (hb3P (γ 0))) kB0b).trans (sub_zero _))
    have kB1b : (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))))) = verschiebungInt (WittVector.teichmuller p (((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) :=
      (hb3V _).trans (congrArg verschiebungInt ((hb3T _ _).trans
        (congrArg (fun s : ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω))) => WittVector.teichmuller p s • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) hpw1)))
    have keyB1 : (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0)))))) = (p : ℕ) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) - verschiebungInt (WittVector.teichmuller p (((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) :=
      (hb3sub ((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))).trans (congr (congrArg (· - ·) (hb3P (γ 1))) kB1b)
    have hns : ∀ u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F, ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((p : ℕ) • u, 0) = p • ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (u, 0) := fun u =>
      (congrArg ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (Prod.ext (Prod.smul_fst p (u, (0 : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F))).symm
        ((smul_zero p).symm.trans (Prod.smul_snd p (u, (0 : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F))).symm))).trans
        (map_nsmul ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk p (u, 0))
    have key0 : ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1)))))), 0) = p • ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))), 0) :=
      (congrArg (fun u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F => ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (u, 0)) keyB0).trans
        ((hns _).trans (congrArg (fun u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F => p • ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (u, 0)) (hred 0).symm))
    have hnV : ∀ u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F, ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (u, 0)) = ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd u, 0) := by
      intro u
      change ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd u, endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd 0) = _
      congr 2 <;> exact map_zero _
    have hsc1 : WittVector.map (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) (WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) = WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) := by
      rw [WittVector.map_teichmuller, hcc]
    have e1 : Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) = verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) :=
      (Rigidified.redC_verschiebungInt ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))).trans (congrArg verschiebungInt (hred 1))
    have e2 : Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) = WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) :=
      (baseChangeEq_smul_witt (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) (Rigidified.XS_F_map_mk ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))) (WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))).trans
        (congr (congrArg (fun (s : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) (u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) => s • u) hsc1) (hred 0))
    have hred1 : Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) = (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) - WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) :=
      (map_sub (Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))) _ _).trans (congr (congrArg (· - ·) e1) e2)
    have hVV : verschiebungInt (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) = p • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))) := by
      rw [← hPiB0, ← endAct_verschiebungInt (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))), ← hPiB0, K81.endAct_varpiEnd_endAct_varpiEnd]
    have hPiComb : endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd ((p : ℕ) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) - verschiebungInt (WittVector.teichmuller p (((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))))) =
        (p : ℕ) • (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) - WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) := by
      have hpp : ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2 = (((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p) ^ p := by rw [← pow_mul, pow_two]
      rw [map_sub (endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd), map_nsmul (endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd), hPiB1]
      rw [endAct_verschiebungInt, endAct_smul_witt, hPiB0, hpp, ← K82Edge.teichmuller_smul_verschiebungInt_eq, hVV]
      exact K81.smul_alg p _ _ _ _
    have keyC : endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0)))))) = (p : ℕ) • (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1)))) - WittVector.teichmuller p ((reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) • (baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))))) :=
      (congrArg (fun u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F => endAct (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).varpiEnd u) keyB1).trans hPiComb
    have key1 : ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0)))))), 0)) = p • ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) (verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))), 0) :=
      (hnV _).trans ((congrArg (fun u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F => ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (u, 0)) keyC).trans
        ((hns _).trans (congrArg (fun u : CartierModule p (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F => p • ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (u, 0)) hred1.symm)))

    have hN0 := (H hOD x).1
    have h1x : (1 : Ω) ∉ x.asIdeal := (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top
    have hR := CerednikDrinfeld.FormalODModule.smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h
      Ω y (Rigidified.awayHom (1 : Ω)) hOD hcbS hcΦS
    have hzred : ∀ e : CartierModule p (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F,
        Rigidified.etaRed ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) hcS hcbS (((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk (e, 0)) = ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) e, 0) := by
      intro e
      change ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) e, Rigidified.redC ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω)) 0) = _
      congr 2 <;> exact map_zero _

    have bridge0 : ((Rigidified.XbarS ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChange (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1)))))), 0) =
        ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1)))))), 0) := rfl
    have bridge1 : ((Rigidified.XbarS ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi
        (((Rigidified.XbarS ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChange (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0)))))), 0)) =
        ((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChangeEq (Ψ := (FormalODModule.map (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X))).F) (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) rfl (baseChangeEq (Ψ := (FormalODModule.map (Ideal.Quotient.mk (pIdeal p Ω)) (FormalODModule.map y X)).F) (Ideal.Quotient.mk (pIdeal p Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0)))))), 0)) := rfl

    have hw : ∀ i : Fin 2, (p : ℚ_[p]) ^ 0 • (Pi.single i 1 : Fin 2 → ℚ_[p]) = fun j => (((Pi.single i 1 : Fin 2 → ℤ_[p]) j : ℤ_[p]) : ℚ_[p]) := by
      intro i
      rw [pow_zero, one_smul]; funext j
      rcases eq_or_ne j i with h | h
      · subst h; simp
      · simp [h]
    have mem0 : (Pi.single 0 1 : Fin 2 → ℚ_[p]) ∈ Q.N₀ x := by
      refine (hN0 _).2 ⟨1, h1x, hcS, hcbS, hcΦS, L, hL, ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0))), 0), ?_⟩
      rw [Rigidified.isEtaSection_zero_iff]
      refine ⟨hz _ hm0 hL0, 0, a, Pi.single 0 1, hw 0, ?_⟩
      rw [hR 0, Matrix.cons_val_zero, hzred, bridge0, key0]
      exact K81.pow_smul_smul p a m _
    have mem1 : (Pi.single 1 1 : Fin 2 → ℚ_[p]) ∈ Q.N₀ x := by
      refine (hN0 _).2 ⟨1, h1x, hcS, hcbS, hcΦS, L, hL, ((FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcS).nMk ((verschiebungInt (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 1))) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) • (baseChangeEq (Ψ := (FormalODModule.map (Rigidified.awayHom (1 : Ω)) (FormalODModule.map y X)).F) (Rigidified.awayHom (1 : Ω)) rfl (baseChangeEq (Ψ := (FormalODModule.map y X).F) y rfl (γ 0)))), 0), ?_⟩
      rw [Rigidified.isEtaSection_zero_iff]
      refine ⟨hz _ hm1 hL1, 0, a, Pi.single 1 1, hw 1, ?_⟩
      rw [hR 1]
      change p ^ (a + m) • ((Rigidified.XbarS ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((Rigidified.XbarS ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk ((baseChange (reduceMap (p := p) (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (((p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1) - (verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0)))))), 0)) = _
      rw [hzred, bridge1, key1]
      exact K81.pow_smul_smul p a m _
    rw [stdLattice_eq_span, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact mem0
    · exact mem1
  exact K81.lattice_of_pi p Q x hPi0 hPi1 hlow

end
end S_CerednikDrinfeld_FormalODModule_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_lattice_eq_of_isCartierQuadruple_map_edge_of_apply_xi_ne_zero (solution)
