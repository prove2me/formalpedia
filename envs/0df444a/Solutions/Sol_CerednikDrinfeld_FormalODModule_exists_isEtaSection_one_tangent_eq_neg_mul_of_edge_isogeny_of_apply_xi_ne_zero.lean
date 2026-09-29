-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bd9c43fa-08bb-5030-bc53-a72d606f029e

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom
import Theorems.Thm_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic
import Theorems.Thm_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_ne_zero
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
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

theorem pi_etaInv_eq_natCast_smul_sub (hξ : ξ = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1) =
      (p : WittVector p R) • δ 0 -
        verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1) := by
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  have h0 := pi_apply_zero j ξ η Y δ hξη hδ ha
  have h1 := pi_one_eq_verschiebungInt_of_left_eq_zero j ξ η Y δ hξ hδ ha
  have hpp : η ^ p ^ 2 = (η ^ p) ^ p := by rw [← pow_mul, sq]
  rw [pi_eq_verschiebungInt_etaInv j ξ η Y δ hξ hδ ha, Nat.cast_smul_eq_nsmul,
    ← CerednikDrinfeld.FormalODModule.endAct_varpiEnd_endAct_varpiEnd Y (δ 0), h0, map_add,
    endAct_smul_witt, endAct_verschiebungInt, h1, h0, hpp]
  simp only [map_sub, map_add, sub_smul, teichmuller_smul_verschiebungInt_eq]
  abel

theorem pi_xiInv_eq_natCast_smul_sub (hη : η = 0) (hδ : Y.IsHomogeneousVBasis j δ)
    (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    endAct Y.varpiEnd (verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0) =
      (p : WittVector p R) • δ 1 -
        verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • δ 0) := by
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  have h1 := pi_apply_one j ξ η Y δ hξη hδ ha
  have h0 := pi_zero_eq_verschiebungInt_of_right_eq_zero j ξ η Y δ hη hδ ha
  have hpp : ξ ^ p ^ 2 = (ξ ^ p) ^ p := by rw [← pow_mul, sq]
  rw [pi_eq_verschiebungInt_xiInv j ξ η Y δ hη hδ ha, Nat.cast_smul_eq_nsmul,
    ← CerednikDrinfeld.FormalODModule.endAct_varpiEnd_endAct_varpiEnd Y (δ 1), h1, map_add,
    endAct_smul_witt, endAct_verschiebungInt, h0, h1, hpp]
  simp only [map_sub, map_add, sub_smul, teichmuller_smul_verschiebungInt_eq]
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

end

namespace K82EtaN

theorem oddVertex_lattice (p : ℕ) [Fact p.Prime] (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (N₁ : Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hmem0 : (Pi.single 0 1 : Fin 2 → ℚ_[p]) ∈ N₁)
    (hmem1 : ((p : ℚ_[p])⁻¹ • (Pi.single 1 1 : Fin 2 → ℚ_[p])) ∈ N₁)
    (hdet1 : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N₁ (-1)) :
    N₁ = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1 := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hu : ((unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) := by
    rw [unitOfNeZero_coe, map_natCast]
  have hL₁ : (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1 =
        latticeMap (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹ * g) (stdLattice ℤ_[p] ℚ_[p]) := by
    show latticeMap _ (latticeMap g (stdLattice ℤ_[p] ℚ_[p])) = _
    rw [latticeMap_mul]
  have hginv : ((scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹ * g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      Matrix.diagonal ![1, (p : ℚ_[p])⁻¹] := by
    rw [Units.val_mul, scalarGL_coe, Units.val_inv_eq_inv_val, hu, hg, map_natCast, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, hpQ]
  have hL₁_le : latticeMap (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹ * g) (stdLattice ℤ_[p] ℚ_[p]) ≤ N₁ := by
    rintro v ⟨w, hw, rfl⟩
    choose a ha using hw
    have hv : mulVecLinR (R := ℤ_[p]) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹ * g) w =
        a 0 • (Pi.single 0 1 : Fin 2 → ℚ_[p]) + a 1 • ((p : ℚ_[p])⁻¹ • (Pi.single 1 1 : Fin 2 → ℚ_[p])) := by
      rw [mulVecLinR_apply, hginv, diagonal_mulVec]
      funext i
      fin_cases i
      · simp [← ha 0, Algebra.smul_def]
      · simp [← ha 1, Algebra.smul_def, mul_comm]
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ hmem0) (Submodule.smul_mem _ _ hmem1)
  have hL₁_det : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p])
      (latticeMap (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹ * g) (stdLattice ℤ_[p] ℚ_[p])) (-1) := by
    refine ⟨_, rfl, 1, ?_⟩
    rw [Matrix.GeneralLinearGroup.val_det_apply, hginv, Matrix.det_diagonal]
    simp [Fin.prod_univ_two, zpow_neg_one]
  have h₁ := (eq_of_le_of_hasDetIndex_padic p _ _ hL₁_le (-1) hL₁_det hdet1).symm
  exact hL₁ ▸ h₁

theorem N₁_le_N₀_of_surjective (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (x : PrimeSpectrum B)
    (hPi0 : Function.Surjective Q.Pi₀) : Q.N₁ x ≤ Q.N₀ x := by
  intro v hv
  refine Q.injective₁ x ⟨v, hv⟩ (Submodule.mem_sup_left ?_)
  rw [Submodule.restrictScalars_mem, LinearMap.mem_range]
  have hs : Function.Surjective (LocalizedModule.map x.asIdeal.primeCompl Q.Pi₀) := by
    unfold LocalizedModule.map
    exact IsLocalizedModule.map_surjective x.asIdeal.primeCompl _ _ Q.Pi₀ hPi0
  exact hs _

theorem nMk_mem_etaPiece (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (i : Fin 2) (z : D.M) (hz : z ∈ D.piece i) (hLz : L z = D.nMk (z, 0)) :
    D.nMk (z, 0) ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i := by
  refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk, hLz, ← map_add,
      Prod.mk_add_mk, add_zero, add_zero]
  · exact AddSubgroup.mem_map.2 ⟨(z, 0), AddSubgroup.mem_prod.2 ⟨hz, zero_mem _⟩, rfl⟩

end K82EtaN

namespace K84Eta

open MvFormalGroup MvFormalGroup.CartierModule

theorem bcEq3_single_one {p : ℕ} [Fact p.Prime] {d : ℕ}
    {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {Φ₀ : MvFormalGroup d R₀} {Φ₁ : MvFormalGroup d R₁} {Φ₂ : MvFormalGroup d R₂} {Φ₃ : MvFormalGroup d R₃}
    [Φ₀.IsComm] [Φ₁.IsComm] [Φ₂.IsComm] [Φ₃.IsComm]
    (δ : Fin 2 → CartierModule p Φ₀) (ξ : R₀)
    (f₁ : R₀ →+* R₁) (f₂ : R₁ →+* R₂) (f₃ : R₂ →+* R₃)
    (h₁ : Φ₀.map f₁ = Φ₁) (h₂ : Φ₁.map f₂ = Φ₂) (h₃ : Φ₂.map f₃ = Φ₃) (hξ : f₁ ξ = 0) :
    baseChangeEq f₃ h₃ (baseChangeEq f₂ h₂ (baseChangeEq f₁ h₁
        ((p : WittVector p R₀) • δ 1 - verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • δ 0)))) =
      (p : WittVector p R₃) • baseChangeEq f₃ h₃ (baseChangeEq f₂ h₂ (baseChangeEq f₁ h₁ (δ 1))) := by
  have hp : p ^ 2 ≠ 0 := pow_ne_zero 2 (Fact.out : p.Prime).ne_zero
  simp only [map_sub, baseChangeEq_smul_witt, baseChangeEq_verschiebungInt, map_natCast,
    WittVector.map_teichmuller, map_pow, hξ, zero_pow hp, WittVector.teichmuller_zero, zero_smul,
    map_zero, sub_zero]

theorem bcEq3_single_zero {p : ℕ} [Fact p.Prime] {d : ℕ}
    {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {Φ₀ : MvFormalGroup d R₀} {Φ₁ : MvFormalGroup d R₁} {Φ₂ : MvFormalGroup d R₂} {Φ₃ : MvFormalGroup d R₃}
    [Φ₀.IsComm] [Φ₁.IsComm] [Φ₂.IsComm] [Φ₃.IsComm]
    (δ : Fin 2 → CartierModule p Φ₀) (η : R₀)
    (f₁ : R₀ →+* R₁) (f₂ : R₁ →+* R₂) (f₃ : R₂ →+* R₃)
    (h₁ : Φ₀.map f₁ = Φ₁) (h₂ : Φ₁.map f₂ = Φ₂) (h₃ : Φ₂.map f₃ = Φ₃) :
    baseChangeEq f₃ h₃ (baseChangeEq f₂ h₂ (baseChangeEq f₁ h₁
        ((p : WittVector p R₀) • δ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1)))) =
      (p : WittVector p R₃) • baseChangeEq f₃ h₃ (baseChangeEq f₂ h₂ (baseChangeEq f₁ h₁ (δ 0))) -
        verschiebungInt (WittVector.teichmuller p ((f₃ (f₂ (f₁ η))) ^ p ^ 2) •
          baseChangeEq f₃ h₃ (baseChangeEq f₂ h₂ (baseChangeEq f₁ h₁ (δ 1)))) := by
  simp only [map_sub, baseChangeEq_smul_witt, baseChangeEq_verschiebungInt, map_natCast,
    WittVector.map_teichmuller, map_pow]

theorem bc3_single_one {p : ℕ} [Fact p.Prime]
    {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (Y : FormalODModule p R₀) (δ : Fin 2 → CartierModule p Y.F) (ξ : R₀)
    (f₁ : R₀ →+* R₁) (f₂ : R₁ →+* R₂) (f₃ : R₂ →+* R₃) (hξ : f₁ ξ = 0) :
    baseChange f₃ (baseChange f₂ (baseChange f₁
        ((p : WittVector p R₀) • δ 1 - verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • δ 0)))) =
      (p : WittVector p R₃) • baseChange f₃ (baseChange f₂ (baseChange f₁ (δ 1))) :=
  bcEq3_single_one δ ξ f₁ f₂ f₃ rfl rfl rfl hξ

theorem bc3_single_zero {p : ℕ} [Fact p.Prime]
    {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (Y : FormalODModule p R₀) (δ : Fin 2 → CartierModule p Y.F) (η : R₀)
    (f₁ : R₀ →+* R₁) (f₂ : R₁ →+* R₂) (f₃ : R₂ →+* R₃) :
    baseChange f₃ (baseChange f₂ (baseChange f₁
        ((p : WittVector p R₀) • δ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1)))) =
      (p : WittVector p R₃) • baseChange f₃ (baseChange f₂ (baseChange f₁ (δ 0))) -
        verschiebungInt (WittVector.teichmuller p ((f₃ (f₂ (f₁ η))) ^ p ^ 2) •
          baseChange f₃ (baseChange f₂ (baseChange f₁ (δ 1)))) :=
  bcEq3_single_zero δ η f₁ f₂ f₃ rfl rfl rfl

theorem locmap_surjective {R : Type} [CommRing R] (S : Submonoid R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (LocalizedModule.map S f) :=
  IsLocalizedModule.map_surjective S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N) f hf

end K84Eta

namespace K83SD

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

theorem exists_eq_teichmuller_smul_add_verschiebung {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  classical
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x

  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.1 hy

  fin_cases i
  ·
    have hdec : x = (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) +
        (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have hz : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 0 := by
      have : x - (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) ∈ D.piece 0 := Submodule.sub_mem _ hx h0
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ hz h1
    refine ⟨c 0, y1, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl
  · have hdec : x = (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) +
        (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have hz : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 1 := by
      have : x - (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) ∈ D.piece 1 := Submodule.sub_mem _ hx h1
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ h0 hz
    refine ⟨c 1, y0, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl

theorem teichmuller_coeff_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (c c' : Fin 2 → B) (y y' : D.M)
    (h : (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y =
      (∑ i : Fin 2, WittVector.teichmuller p (c' i) • γ i) + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y)
  have h1 : (c, y) = cy := huniq (c, y) rfl
  have h2 : (c', y') = cy := huniq (c', y') h
  have := h1.trans h2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem fin_two_add_one_add_one (l : Fin 2) : l + 1 + 1 = l := by
  fin_cases l <;> rfl

theorem exists_piece_split (l : Fin 2) (g : D.M) :
    ∃ g₁ ∈ D.piece l, ∃ g₂ ∈ D.piece (l + 1), g = g₁ + g₂ := by
  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hg : g ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨g0, hg0, g1, hg1, rfl⟩ := Submodule.mem_sup.1 hg
  fin_cases l
  · exact ⟨g0, hg0, g1, hg1, rfl⟩
  · exact ⟨g1, hg1, g0, hg0, add_comm _ _⟩

theorem eq_zero_of_mem_piece_of_mem_piece_add_one (l : Fin 2) (m : D.M) (h₁ : m ∈ D.piece l)
    (h₂ : m ∈ D.piece (l + 1)) : m = 0 := by
  have hd := D.isCompl_piece.disjoint
  rw [Submodule.disjoint_def] at hd
  fin_cases l
  · exact hd _ h₁ h₂
  · exact hd _ h₂ h₁

theorem mem_piece_of_verschiebung_mem (hV : Function.Injective D.verschiebung) (l : Fin 2) (g : D.M)
    (hg : D.verschiebung g ∈ D.piece (l + 1)) : g ∈ D.piece l := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := exists_piece_split D l g
  have h2 : D.verschiebung g₂ ∈ D.piece l := by
    have := D.verschiebung_mem (l + 1) g₂ hg₂
    rwa [fin_two_add_one_add_one] at this
  have h2' : D.verschiebung g₂ ∈ D.piece (l + 1) := by
    have h1 : D.verschiebung g₁ ∈ D.piece (l + 1) := D.verschiebung_mem l g₁ hg₁
    have := Submodule.sub_mem _ hg h1
    rwa [map_add, add_sub_cancel_left] at this
  have hz : D.verschiebung g₂ = 0 := eq_zero_of_mem_piece_of_mem_piece_add_one D l _ h2 h2'
  have : g₂ = 0 := hV (by rw [hz, map_zero])
  rw [this, add_zero]
  exact hg₁

theorem exists_eq_teichmuller_smul_add_verschiebung' {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), m ∈ D.piece (i + 1) ∧ x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  obtain ⟨c, m, hxm⟩ := exists_eq_teichmuller_smul_add_verschiebung D hγ i x hx
  refine ⟨c, m, ?_, hxm⟩
  apply mem_piece_of_verschiebung_mem D hγ.verschiebung_injective
  rw [fin_two_add_one_add_one]
  have := Submodule.sub_mem _ hx (Submodule.smul_mem _ (WittVector.teichmuller p c) (hγ.1 i))
  rwa [hxm, add_sub_cancel_left] at this

theorem mem_nPiece_iff (l : Fin 2) (z : D.NMod) :
    z ∈ D.nPiece l ↔ ∃ m m' : D.M, m ∈ D.piece l ∧ m' ∈ D.piece l ∧ D.nMk (m, m') = z := by
  constructor
  · rintro ⟨⟨m, m'⟩, hmm, rfl⟩
    exact ⟨m, m', hmm.1, hmm.2, rfl⟩
  · rintro ⟨m, m', hm, hm', rfl⟩
    exact ⟨(m, m'), ⟨hm, hm'⟩, rfl⟩

theorem nMk_mem_nPiece (l : Fin 2) {m m' : D.M} (hm : m ∈ D.piece l) (hm' : m' ∈ D.piece l) :
    D.nMk (m, m') ∈ D.nPiece l :=
  (mem_nPiece_iff D l _).2 ⟨m, m', hm, hm', rfl⟩

theorem smul_mem_nPiece (l : Fin 2) (w : WittVector p B) {z : D.NMod} (hz : z ∈ D.nPiece l) :
    w • z ∈ D.nPiece l := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [smul_nMk]
  exact nMk_mem_nPiece D l (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hm')

theorem lambda_mem_piece (l : Fin 2) {z : D.NMod} (hz : z ∈ D.nPiece l) : D.lambda z ∈ D.piece (l + 1) := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [lambda_nMk]
  exact Submodule.add_mem _ (D.varpi_mem l m hm) (D.verschiebung_mem l m' hm')

theorem teichmuller_smul_eq_sum (γ : Fin 2 → D.M) (i : Fin 2) (c : B) :
    WittVector.teichmuller p c • γ i =
      ∑ r : Fin 2, WittVector.teichmuller p ((if r = i then c else 0 : B)) • γ r := by
  fin_cases i <;> simp [Fin.sum_univ_two, WittVector.teichmuller_zero]

theorem digit_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) (i : Fin 2) (c c' : B) (y y' : D.M)
    (h : WittVector.teichmuller p c • γ i + D.verschiebung y =
      WittVector.teichmuller p c' • γ i + D.verschiebung y') : c = c' ∧ y = y' := by
  rw [teichmuller_smul_eq_sum D γ i c, teichmuller_smul_eq_sum D γ i c'] at h
  obtain ⟨hcc, hyy⟩ := teichmuller_coeff_unique D hγ _ _ y y' h
  have := congrFun hcc i
  simp only [] at this
  exact ⟨by simpa using this, hyy⟩

theorem nsmul_eq_verschiebung_verschiebung (n : D.M) (hn : D.varpi n = D.verschiebung n) :
    p • n = D.verschiebung (D.verschiebung n) := by
  rw [← D.varpi_varpi, hn, D.varpi_verschiebung, hn]

end Datum

section Law

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (jR : Zp2 p →+* R)
  (X : FormalODModule p R) (hc : IsCompl (X.gradedPiece jR 0) (X.gradedPiece jR 1))

theorem crit_of_basis (γ : Fin 2 → (X.toGradedCartierModuleData jR hc).M)
    (hγ : (X.toGradedCartierModuleData jR hc).IsHomogeneousVBasis γ) (i : Fin 2) (xi : (X.toGradedCartierModuleData jR hc).M)
    (hcrit : (X.toGradedCartierModuleData jR hc).varpi (γ i) = (X.toGradedCartierModuleData jR hc).verschiebung xi) :
    ∀ m ∈ X.gradedPiece jR (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  intro m hm
  obtain ⟨c, m', hmm⟩ := exists_eq_teichmuller_smul_add_verschiebung (X.toGradedCartierModuleData jR hc) hγ i m hm
  refine ⟨(WittVector.frobenius (WittVector.teichmuller p c) • xi + (X.toGradedCartierModuleData jR hc).varpi m' :
    (X.toGradedCartierModuleData jR hc).M), ?_⟩
  have : (X.toGradedCartierModuleData jR hc).varpi m =
      (X.toGradedCartierModuleData jR hc).verschiebung
        (WittVector.frobenius (WittVector.teichmuller p c) • xi + (X.toGradedCartierModuleData jR hc).varpi m') := by
    rw [hmm, map_add, map_smul, hcrit, (X.toGradedCartierModuleData jR hc).smul_verschiebung,
      (X.toGradedCartierModuleData jR hc).varpi_verschiebung, ← map_add]
  exact this.symm

variable [CharP R p]

theorem nMk_mem_etaPiece (L : (X.toGradedCartierModuleData jR hc).M →+ (X.toGradedCartierModuleData jR hc).NMod)
    (hL : (X.toGradedCartierModuleData jR hc).IsCanonicalLMap L) (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece jR (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m)
    (n : CartierModule p X.F) (hn : n ∈ X.gradedPiece jR (i : ℕ))
    (hinv : endAct X.varpiEnd n = verschiebungInt n) :
    (X.toGradedCartierModuleData jR hc).nMk (n, 0) ∈
      (X.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung i := by
  have hLe : L n = (X.toGradedCartierModuleData jR hc).nMk (n, 0) :=
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p jR X hc L hL (i : ℕ) hi n n hn hinv.symm
  refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_eta_iff, phi_nMk, hLe, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  · exact AddSubgroup.mem_map.2 ⟨(n, 0), AddSubgroup.mem_prod.2 ⟨hn, zero_mem _⟩, rfl⟩

end Law

theorem hasHeight_map_field {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B)
    (hX4 : X.HasHeight 4) {K : Type} [Field K] (g : B →+* K) : (X.map g).HasHeight 4 := by
  obtain ⟨-, -, hfib⟩ := hX4
  have hK : Module.finrank K (FormalODModule.KerAlgebra ((X.act (p : Zp2 p)).map g)) = p ^ 4 := hfib K g
  show FormalODModule.HasKernelOfDegree ((X.map g).act (p : Zp2 p)) (p ^ 4)
  rw [FormalODModule.map_act]
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · exact Module.finite_of_finrank_pos (by rw [hK]; exact pow_pos (Nat.Prime.pos Fact.out) 4)
  · exact Module.Projective.of_free
  · rw [CerednikDrinfeld.SpecialFormal.Series.map_map]; exact hfib κ (f.comp g)

theorem isHausdorff_of_eq_zero {p : ℕ} {S : Type} [CommRing S] (hS : ((p : ℕ) : S) = 0) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  refine ⟨fun x hx => ?_⟩
  have := hx 1
  rwa [pow_one, hS, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

end K83SD

noncomputable section

namespace K83Sec0

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]
variable {R : Type} [CommRing R] (jR : Zp2 p →+* R) (Y : FormalODModule p R)
  (hc : IsCompl (Y.gradedPiece jR 0) (Y.gradedPiece jR 1))

theorem nVarpi_nMk (m m' : (Y.toGradedCartierModuleData jR hc).M) : (Y.toGradedCartierModuleData jR hc).nVarpi ((Y.toGradedCartierModuleData jR hc).nMk (m, m')) = (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).varpi m, (Y.toGradedCartierModuleData jR hc).varpi m') := rfl

theorem nVarpi_eq_nMk_lambda (z : (Y.toGradedCartierModuleData jR hc).NMod) : (Y.toGradedCartierModuleData jR hc).nVarpi z = (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).lambda z, 0) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := (Y.toGradedCartierModuleData jR hc).nMk_surjective z
  rw [lambda_nMk, nVarpi_nMk]
  have h : (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).verschiebung x', 0) = (Y.toGradedCartierModuleData jR hc).nMk (0, (Y.toGradedCartierModuleData jR hc).varpi x') := by
    have := (Y.toGradedCartierModuleData jR hc).nMk_verschiebung_neg_varpi x'
    rw [← sub_eq_zero, ← map_sub, Prod.mk_sub_mk, sub_zero, zero_sub]
    exact this
  have e1 : (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).varpi x + (Y.toGradedCartierModuleData jR hc).verschiebung x', 0) = (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).varpi x, 0) + (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).verschiebung x', 0) := by
    rw [← map_add, Prod.mk_add_mk, add_zero]
  have e2 : (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).varpi x, (Y.toGradedCartierModuleData jR hc).varpi x') = (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).varpi x, 0) + (Y.toGradedCartierModuleData jR hc).nMk (0, (Y.toGradedCartierModuleData jR hc).varpi x') := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [e1, e2, h]

theorem nsmul_eq_nVarpi_nVarpi (z : (Y.toGradedCartierModuleData jR hc).NMod) : (p : ℕ) • z = (Y.toGradedCartierModuleData jR hc).nVarpi ((Y.toGradedCartierModuleData jR hc).nVarpi z) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := (Y.toGradedCartierModuleData jR hc).nMk_surjective z
  rw [nVarpi_nMk, nVarpi_nMk, (Y.toGradedCartierModuleData jR hc).varpi_varpi, (Y.toGradedCartierModuleData jR hc).varpi_varpi, ← map_nsmul, Prod.smul_mk]

theorem exists_nMk_of_mem_nPiece (i : Fin 2) (z : (Y.toGradedCartierModuleData jR hc).NMod) (hz : z ∈ (Y.toGradedCartierModuleData jR hc).nPiece i) :
    ∃ x x' : CartierModule p Y.F, x ∈ Y.gradedPiece jR (i : ℕ) ∧ x' ∈ Y.gradedPiece jR (i : ℕ) ∧ z = (Y.toGradedCartierModuleData jR hc).nMk (x, x') := by
  obtain ⟨⟨x, x'⟩, hxx, rfl⟩ := AddSubgroup.mem_map.mp hz
  obtain ⟨hx, hx'⟩ := AddSubgroup.mem_prod.mp hxx
  exact ⟨x, x', hx, hx', rfl⟩

theorem u_apply_eq_mkQ (L : (Y.toGradedCartierModuleData jR hc).M →+ (Y.toGradedCartierModuleData jR hc).NMod) (hLv : ∀ x : (Y.toGradedCartierModuleData jR hc).M, L ((Y.toGradedCartierModuleData jR hc).verschiebung x) = (Y.toGradedCartierModuleData jR hc).nMk ((Y.toGradedCartierModuleData jR hc).varpi x, 0))
    (x x' : CartierModule p Y.F) (hz : (Y.toGradedCartierModuleData jR hc).nMk (x, x') ∈ (Y.toGradedCartierModuleData jR hc).eta L hLv) :
    (Y.toGradedCartierModuleData jR hc).u L hLv ⟨(Y.toGradedCartierModuleData jR hc).nMk (x, x'), hz⟩ = (Y.toGradedCartierModuleData jR hc).vRange.mkQ x := rfl

variable (δ : Fin 2 → CartierModule p Y.F)

theorem exists_tangent_ne_zero [Nontrivial R] (hδ : Y.IsHomogeneousVBasis jR δ) (i : Fin 2) :
    ∃ k : Fin 2, tangent (δ i) k ≠ 0 := by
  by_contra h
  push_neg at h
  have hdet : (Matrix.of fun i k => tangent (δ i) k).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero i (fun k => h k)
  exact not_isUnit_zero (hdet ▸ hδ.2)

theorem eq_zero_of_mul_tangent_eq_zero (hδ : Y.IsHomogeneousVBasis jR δ) (i : Fin 2) (c : R)
    (h : ∀ k : Fin 2, c * tangent (δ i) k = 0) : c = 0 := by
  set T : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i k => tangent (δ i) k with hT
  have hT0 : Matrix.vecMul (Pi.single i c) T = 0 := by
    funext k
    rw [Matrix.single_vecMul]
    show c • T i k = 0
    rw [hT, Matrix.of_apply, smul_eq_mul, h k]
  have key : Pi.single i c = Matrix.vecMul (Matrix.vecMul (Pi.single i c) T) T⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (by rw [hT]; exact hδ.2), Matrix.vecMul_one]
  rw [hT0, Matrix.zero_vecMul] at key
  simpa using congrFun key i

variable [CharP R p] (ξ η : R)

include hc in

theorem exists_verschiebungInt_eq_of_varpi (hξ : ξ = 0) (hu : IsUnit (η ^ p - η))
    (hδ : Y.IsHomogeneousVBasis jR δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    ∀ m ∈ Y.gradedPiece jR ((0 : Fin 2) : ℕ),
      (∃ g : CartierModule p Y.F, verschiebungInt g = endAct Y.varpiEnd m) →
        ∃ g' : CartierModule p Y.F, verschiebungInt g' = m := by
  intro m hm hg
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hγD, -⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p jR Y δ hδ hc
  obtain ⟨α, y, hmy⟩ := K83SD.exists_eq_teichmuller_smul_add_verschiebung (Y.toGradedCartierModuleData jR hc) hγD 0 m hm
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  have hPi0 := K82Edge.pi_apply_zero jR ξ η Y δ hξη hδ ha
  have h0 : tangent (endAct Y.varpiEnd m) = 0 := by rw [← hg, tangent_verschiebungInt]
  have h1 : tangent (endAct Y.varpiEnd m) = (α * (η ^ p - η)) • tangent (δ 1) := by
    have hmy' : m = WittVector.teichmuller p α • δ 0 + verschiebungInt y := hmy
    rw [hmy', map_add, endAct_smul_witt, endAct_verschiebungInt, hPi0, map_add, tangent_verschiebungInt, add_zero,
      tangent_smul_witt, map_add, tangent_verschiebungInt, add_zero, K82Edge.tangent_teichmuller_sub_smul, smul_smul,
      WittVector.teichmuller_coeff_zero]
  have hα : α = 0 := by
    obtain ⟨w, hw⟩ := hu
    have h2 : α * (η ^ p - η) = 0 :=
      eq_zero_of_mul_tangent_eq_zero jR Y δ hδ 1 _ (fun k => by
        have := congrFun (h0 ▸ h1).symm k
        simpa [Pi.smul_apply, smul_eq_mul] using this)
    have : α * (η ^ p - η) * ↑w⁻¹ = 0 := by rw [h2, zero_mul]
    rwa [← hw, mul_assoc, Units.mul_inv, mul_one] at this
  refine ⟨y, ?_⟩
  have hmy' : m = WittVector.teichmuller p α • δ 0 + verschiebungInt y := hmy
  rw [hmy', hα, WittVector.teichmuller_zero, zero_smul, zero_add]

omit [CharP R p] in

theorem exists_smul_eq_add_verschiebungInt (c : WittVector p R) (hc1 : WittVector.constantCoeff c = 1)
    (f : CartierModule p Y.F) :
    ∃ g : CartierModule p Y.F, c • f = f + verschiebungInt g := by
  have h0 : ∀ i < 1, (c - 1).coeff i = 0 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, hc1, sub_self]
  have hcV : c - 1 = WittVector.verschiebung ((c - 1).shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := c - 1) (n := 1) h0
    rwa [Function.iterate_one] at this
  refine ⟨(c - 1).shift 1 • MvFormalGroup.CartierModule.frobenius f, ?_⟩
  have key : verschiebungInt ((c - 1).shift 1 • MvFormalGroup.CartierModule.frobenius f) = (c - 1) • f := by
    have := verschiebungInt_smul_frobenius (Φ := Y.F) ((c - 1).shift 1) f
    rw [← hcV] at this
    exact this
  rw [key, sub_smul, one_smul, add_sub_cancel]

include hc in

theorem exists_sections_zero [Nontrivial R] (hξ : ξ = 0) (hu : IsUnit (η ^ p - η))
    (hδ : Y.IsHomogeneousVBasis jR δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η))
    (L : (Y.toGradedCartierModuleData jR hc).M →+ (Y.toGradedCartierModuleData jR hc).NMod) (hL : (Y.toGradedCartierModuleData jR hc).IsCanonicalLMap L) :
    ∃ (z₀ z₁ : (Y.toGradedCartierModuleData jR hc).NMod)
      (hz₀ : z₀ ∈ (Y.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung 0)
      (hz₁ : z₁ ∈ (Y.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung 0),
      (Y.toGradedCartierModuleData jR hc).nVarpi z₀ = (Y.toGradedCartierModuleData jR hc).nMk (δ 1, 0) ∧
      (Y.toGradedCartierModuleData jR hc).nVarpi z₁ = (Y.toGradedCartierModuleData jR hc).nMk (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1, 0) ∧
      ∃ (m₀ m₁ : CartierModule p Y.F),
        (Y.toGradedCartierModuleData jR hc).vRange.mkQ m₀ = (Y.toGradedCartierModuleData jR hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀).1⟩ ∧
        (Y.toGradedCartierModuleData jR hc).vRange.mkQ m₁ = (Y.toGradedCartierModuleData jR hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁).1⟩ ∧
        (∀ k : Fin 2, tangent m₁ k = -η * tangent m₀ k) ∧
        ∃ k : Fin 2, tangent m₀ k ≠ 0 := by
  classical
  have hξη : ξ * η = 0 := by rw [hξ, zero_mul]
  have hinj := exists_verschiebungInt_eq_of_varpi jR Y hc δ ξ η hξ hu hδ ha
  obtain ⟨w, hw⟩ := hu
  have hPi0 : endAct Y.varpiEnd (δ 0) =
      (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) • δ 1 + verschiebungInt (δ 0) :=
    K82Edge.pi_apply_zero jR ξ η Y δ hξη hδ ha
  have hPi1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1) :=
    K82Edge.pi_one_eq_verschiebungInt_of_left_eq_zero jR ξ η Y δ hξ hδ ha
  have hPiinv : endAct Y.varpiEnd (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1) =
      verschiebungInt (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1) :=
    K82Edge.pi_eq_verschiebungInt_etaInv jR ξ η Y δ hξ hδ ha
  have hB := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
    p jR Y hc L hL 0 hinj

  set b : R := ((w⁻¹ : Rˣ) : R) with hb
  have hab : (η ^ p - η) * b = 1 := by rw [hb, ← hw, Units.mul_inv]
  set c : WittVector p R :=
    WittVector.teichmuller p b * (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) with hcdef
  have hc1 : WittVector.constantCoeff c = 1 := by
    rw [hcdef, map_mul, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_zero, mul_comm, hab]
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq_add_verschiebungInt Y c hc1 (δ 1)

  have hPib : endAct Y.varpiEnd (WittVector.teichmuller p b • δ 0) =
      δ 1 + verschiebungInt (g₁ + WittVector.teichmuller p (b ^ p) • δ 0) := by
    rw [endAct_smul_witt, hPi0, smul_add, smul_smul, K82Edge.teichmuller_smul_verschiebungInt_eq, ← hcdef, hg₁, map_add,
      add_assoc]

  have hdec1 : δ 1 = endAct Y.varpiEnd (WittVector.teichmuller p b • δ 0) +
      verschiebungInt (-(g₁ + WittVector.teichmuller p (b ^ p) • δ 0)) := by
    rw [hPib, map_neg, add_neg_cancel_right]

  have hdec2 : verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1 =
      endAct Y.varpiEnd (-(WittVector.teichmuller p η • (WittVector.teichmuller p b • δ 0))) +
        verschiebungInt (δ 0 + WittVector.teichmuller p (η ^ p) • (g₁ + WittVector.teichmuller p (b ^ p) • δ 0)) := by
    rw [map_neg, endAct_smul_witt, hPib, smul_add, K82Edge.teichmuller_smul_verschiebungInt_eq, map_add]
    abel

  have hδ0 : δ 0 ∈ (Y.toGradedCartierModuleData jR hc).piece 0 := hδ.1 0
  have hδ1 : δ 1 ∈ (Y.toGradedCartierModuleData jR hc).piece 1 := hδ.1 1
  have hx1 : WittVector.teichmuller p b • δ 0 ∈ (Y.toGradedCartierModuleData jR hc).piece 0 := Submodule.smul_mem _ _ hδ0
  have hx2 : -(WittVector.teichmuller p η • (WittVector.teichmuller p b • δ 0)) ∈ (Y.toGradedCartierModuleData jR hc).piece 0 :=
    Submodule.neg_mem _ (Submodule.smul_mem _ _ hx1)
  have hinv1 : verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1 ∈ (Y.toGradedCartierModuleData jR hc).piece 1 :=
    Submodule.sub_mem _ ((Y.toGradedCartierModuleData jR hc).verschiebung_mem 0 _ hδ0) (Submodule.smul_mem _ _ hδ1)

  have ht1 : δ 1 ∈ {m : MvFormalGroup.CartierModule p Y.F | m ∈ Y.gradedPiece jR (((0 : Fin 2) + 1 : Fin 2) : ℕ) ∧
        MvFormalGroup.CartierModule.endAct Y.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        ∃ x ∈ Y.gradedPiece jR ((0 : Fin 2) : ℕ), ∃ x' : MvFormalGroup.CartierModule p Y.F,
          m = MvFormalGroup.CartierModule.endAct Y.varpiEnd x + MvFormalGroup.CartierModule.verschiebungInt x'} :=
    ⟨hδ1, hPi1, _, hx1, _, hdec1⟩
  have ht2 : verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1 ∈
      {m : MvFormalGroup.CartierModule p Y.F | m ∈ Y.gradedPiece jR (((0 : Fin 2) + 1 : Fin 2) : ℕ) ∧
        MvFormalGroup.CartierModule.endAct Y.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        ∃ x ∈ Y.gradedPiece jR ((0 : Fin 2) : ℕ), ∃ x' : MvFormalGroup.CartierModule p Y.F,
          m = MvFormalGroup.CartierModule.endAct Y.varpiEnd x + MvFormalGroup.CartierModule.verschiebungInt x'} :=
    ⟨hinv1, hPiinv, _, hx2, _, hdec2⟩
  obtain ⟨z₀, hz₀, hlz₀⟩ := hB.surjOn ht1
  obtain ⟨z₁, hz₁, hlz₁⟩ := hB.surjOn ht2

  obtain ⟨x₀, x₀', hx₀, hx₀', rfl⟩ := exists_nMk_of_mem_nPiece jR Y hc 0 z₀ (AddSubgroup.mem_inf.mp hz₀).2
  obtain ⟨x₁, x₁', hx₁, hx₁', rfl⟩ := exists_nMk_of_mem_nPiece jR Y hc 0 z₁ (AddSubgroup.mem_inf.mp hz₁).2
  rw [lambda_nMk] at hlz₀ hlz₁

  have hV0 : ∃ g : CartierModule p Y.F, verschiebungInt g = x₀ - WittVector.teichmuller p b • δ 0 := by
    refine hinj _ (Submodule.sub_mem _ hx₀ hx1) ⟨-(g₁ + WittVector.teichmuller p (b ^ p) • δ 0) - x₀', ?_⟩
    have e : endAct Y.varpiEnd x₀ + verschiebungInt x₀' =
        endAct Y.varpiEnd (WittVector.teichmuller p b • δ 0) + verschiebungInt (-(g₁ + WittVector.teichmuller p (b ^ p) • δ 0)) :=
      hlz₀.trans hdec1
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
  have hV1 : ∃ g : CartierModule p Y.F, verschiebungInt g = x₁ - -(WittVector.teichmuller p η • (WittVector.teichmuller p b • δ 0)) := by
    refine hinj _ (Submodule.sub_mem _ hx₁ hx2) ⟨(δ 0 + WittVector.teichmuller p (η ^ p) • (g₁ + WittVector.teichmuller p (b ^ p) • δ 0)) - x₁', ?_⟩
    have e : endAct Y.varpiEnd x₁ + verschiebungInt x₁' =
        endAct Y.varpiEnd (-(WittVector.teichmuller p η • (WittVector.teichmuller p b • δ 0))) +
          verschiebungInt (δ 0 + WittVector.teichmuller p (η ^ p) • (g₁ + WittVector.teichmuller p (b ^ p) • δ 0)) :=
      hlz₁.trans hdec2
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
  refine ⟨(Y.toGradedCartierModuleData jR hc).nMk (x₀, x₀'), (Y.toGradedCartierModuleData jR hc).nMk (x₁, x₁'), hz₀, hz₁, ?_, ?_, WittVector.teichmuller p b • δ 0,
    -(WittVector.teichmuller p η • (WittVector.teichmuller p b • δ 0)), ?_, ?_, ?_, ?_⟩
  · rw [nVarpi_eq_nMk_lambda, lambda_nMk]; exact congrArg (fun m => (Y.toGradedCartierModuleData jR hc).nMk (m, 0)) hlz₀
  · rw [nVarpi_eq_nMk_lambda, lambda_nMk]; exact congrArg (fun m => (Y.toGradedCartierModuleData jR hc).nMk (m, 0)) hlz₁
  ·
    rw [u_apply_eq_mkQ]
    obtain ⟨g, hg⟩ := hV0
    symm
    exact (Submodule.Quotient.eq _).2 ⟨g, hg⟩
  · rw [u_apply_eq_mkQ]
    obtain ⟨g, hg⟩ := hV1
    symm
    exact (Submodule.Quotient.eq _).2 ⟨g, hg⟩
  · intro k
    rw [map_neg, tangent_smul_witt, tangent_smul_witt, Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    erw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    rw [neg_mul]
  · obtain ⟨k, hk⟩ := exists_tangent_ne_zero jR Y δ hδ 0
    refine ⟨k, ?_⟩
    rw [tangent_smul_witt, Pi.smul_apply, smul_eq_mul]
    erw [WittVector.teichmuller_coeff_zero]
    intro h0
    apply hk
    have : (η ^ p - η) * (b * tangent (δ 0) k) = 0 := by rw [h0, mul_zero]
    rwa [← mul_assoc, hab, one_mul] at this

section Xi

variable [CharP R p] (ξ η : R)

include hc in

theorem exists_verschiebungInt_eq_of_varpi_one (hη : η = 0) (hu : IsUnit (ξ ^ p - ξ))
    (hδ : Y.IsHomogeneousVBasis jR δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η)) :
    ∀ m ∈ Y.gradedPiece jR ((1 : Fin 2) : ℕ),
      (∃ g : CartierModule p Y.F, verschiebungInt g = endAct Y.varpiEnd m) →
        ∃ g' : CartierModule p Y.F, verschiebungInt g' = m := by
  intro m hm hg
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hγD, -⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p jR Y δ hδ hc
  obtain ⟨α, y, hmy⟩ := K83SD.exists_eq_teichmuller_smul_add_verschiebung (Y.toGradedCartierModuleData jR hc) hγD 1 m hm
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  have hPi1 := K82Edge.pi_apply_one jR ξ η Y δ hξη hδ ha
  have h0 : tangent (endAct Y.varpiEnd m) = 0 := by rw [← hg, tangent_verschiebungInt]
  have h1 : tangent (endAct Y.varpiEnd m) = (α * (ξ ^ p - ξ)) • tangent (δ 0) := by
    have hmy' : m = WittVector.teichmuller p α • δ 1 + verschiebungInt y := hmy
    rw [hmy', map_add, endAct_smul_witt, endAct_verschiebungInt, hPi1, map_add, tangent_verschiebungInt, add_zero,
      tangent_smul_witt, map_add, tangent_verschiebungInt, add_zero, K82Edge.tangent_teichmuller_sub_smul, smul_smul,
      WittVector.teichmuller_coeff_zero]
  have hα : α = 0 := by
    obtain ⟨w, hw⟩ := hu
    have h2 : α * (ξ ^ p - ξ) = 0 :=
      eq_zero_of_mul_tangent_eq_zero jR Y δ hδ 0 _ (fun k => by
        have := congrFun (h0 ▸ h1).symm k
        simpa [Pi.smul_apply, smul_eq_mul] using this)
    have : α * (ξ ^ p - ξ) * ↑w⁻¹ = 0 := by rw [h2, zero_mul]
    rwa [← hw, mul_assoc, Units.mul_inv, mul_one] at this
  refine ⟨y, ?_⟩
  have hmy' : m = WittVector.teichmuller p α • δ 1 + verschiebungInt y := hmy
  rw [hmy', hα, WittVector.teichmuller_zero, zero_smul, zero_add]

include hc in

theorem exists_sections_one [Nontrivial R] (hη : η = 0) (hu : IsUnit (ξ ^ p - ξ))
    (hδ : Y.IsHomogeneousVBasis jR δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p ξ η))
    (L : (Y.toGradedCartierModuleData jR hc).M →+ (Y.toGradedCartierModuleData jR hc).NMod) (hL : (Y.toGradedCartierModuleData jR hc).IsCanonicalLMap L) :
    ∃ (z₀ z₁ : (Y.toGradedCartierModuleData jR hc).NMod)
      (hz₀ : z₀ ∈ (Y.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung 1)
      (hz₁ : z₁ ∈ (Y.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung 1),
      (Y.toGradedCartierModuleData jR hc).nVarpi z₀ = (Y.toGradedCartierModuleData jR hc).nMk (δ 0, 0) ∧
      (Y.toGradedCartierModuleData jR hc).nVarpi z₁ = (Y.toGradedCartierModuleData jR hc).nMk (verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0, 0) ∧
      ∃ (m₀ m₁ : CartierModule p Y.F),
        (Y.toGradedCartierModuleData jR hc).vRange.mkQ m₀ = (Y.toGradedCartierModuleData jR hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀).1⟩ ∧
        (Y.toGradedCartierModuleData jR hc).vRange.mkQ m₁ = (Y.toGradedCartierModuleData jR hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁).1⟩ ∧
        (∀ k : Fin 2, tangent m₁ k = -ξ * tangent m₀ k) ∧
        ∃ k : Fin 2, tangent m₀ k ≠ 0 := by
  classical
  have hξη : ξ * η = 0 := by rw [hη, mul_zero]
  have hinj := exists_verschiebungInt_eq_of_varpi_one jR Y hc δ ξ η hη hu hδ ha
  obtain ⟨w, hw⟩ := hu
  have hPi1 : endAct Y.varpiEnd (δ 1) =
      (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • δ 0 + verschiebungInt (δ 1) :=
    K82Edge.pi_apply_one jR ξ η Y δ hξη hδ ha
  have hPi0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0) :=
    K82Edge.pi_zero_eq_verschiebungInt_of_right_eq_zero jR ξ η Y δ hη hδ ha
  have hPiinv : endAct Y.varpiEnd (verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0) =
      verschiebungInt (verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0) :=
    K82Edge.pi_eq_verschiebungInt_xiInv jR ξ η Y δ hη hδ ha
  have hB := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
    p jR Y hc L hL 1 hinj
  set b : R := ((w⁻¹ : Rˣ) : R) with hb
  have hab : (ξ ^ p - ξ) * b = 1 := by rw [hb, ← hw, Units.mul_inv]
  set c : WittVector p R :=
    WittVector.teichmuller p b * (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) with hcdef
  have hc1 : WittVector.constantCoeff c = 1 := by
    rw [hcdef, map_mul, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_zero, mul_comm, hab]
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq_add_verschiebungInt Y c hc1 (δ 0)
  have hPib : endAct Y.varpiEnd (WittVector.teichmuller p b • δ 1) =
      δ 0 + verschiebungInt (g₁ + WittVector.teichmuller p (b ^ p) • δ 1) := by
    rw [endAct_smul_witt, hPi1, smul_add, smul_smul, K82Edge.teichmuller_smul_verschiebungInt_eq, ← hcdef, hg₁, map_add,
      add_assoc]
  have hdec1 : δ 0 = endAct Y.varpiEnd (WittVector.teichmuller p b • δ 1) +
      verschiebungInt (-(g₁ + WittVector.teichmuller p (b ^ p) • δ 1)) := by
    rw [hPib, map_neg, add_neg_cancel_right]
  have hdec2 : verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0 =
      endAct Y.varpiEnd (-(WittVector.teichmuller p ξ • (WittVector.teichmuller p b • δ 1))) +
        verschiebungInt (δ 1 + WittVector.teichmuller p (ξ ^ p) • (g₁ + WittVector.teichmuller p (b ^ p) • δ 1)) := by
    rw [map_neg, endAct_smul_witt, hPib, smul_add, K82Edge.teichmuller_smul_verschiebungInt_eq, map_add]
    abel
  have hδ0 : δ 0 ∈ (Y.toGradedCartierModuleData jR hc).piece 0 := hδ.1 0
  have hδ1 : δ 1 ∈ (Y.toGradedCartierModuleData jR hc).piece 1 := hδ.1 1
  have hx1 : WittVector.teichmuller p b • δ 1 ∈ (Y.toGradedCartierModuleData jR hc).piece 1 := Submodule.smul_mem _ _ hδ1
  have hx2 : -(WittVector.teichmuller p ξ • (WittVector.teichmuller p b • δ 1)) ∈ (Y.toGradedCartierModuleData jR hc).piece 1 :=
    Submodule.neg_mem _ (Submodule.smul_mem _ _ hx1)
  have hinv1 : verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0 ∈ (Y.toGradedCartierModuleData jR hc).piece 0 := by
    have := (Y.toGradedCartierModuleData jR hc).verschiebung_mem 1 _ hδ1
    exact Submodule.sub_mem _ this (Submodule.smul_mem _ _ hδ0)
  have ht1 : δ 0 ∈ {m : MvFormalGroup.CartierModule p Y.F | m ∈ Y.gradedPiece jR (((1 : Fin 2) + 1 : Fin 2) : ℕ) ∧
        MvFormalGroup.CartierModule.endAct Y.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        ∃ x ∈ Y.gradedPiece jR ((1 : Fin 2) : ℕ), ∃ x' : MvFormalGroup.CartierModule p Y.F,
          m = MvFormalGroup.CartierModule.endAct Y.varpiEnd x + MvFormalGroup.CartierModule.verschiebungInt x'} :=
    ⟨hδ0, hPi0, _, hx1, _, hdec1⟩
  have ht2 : verschiebungInt (δ 1) - WittVector.teichmuller p ξ • δ 0 ∈
      {m : MvFormalGroup.CartierModule p Y.F | m ∈ Y.gradedPiece jR (((1 : Fin 2) + 1 : Fin 2) : ℕ) ∧
        MvFormalGroup.CartierModule.endAct Y.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        ∃ x ∈ Y.gradedPiece jR ((1 : Fin 2) : ℕ), ∃ x' : MvFormalGroup.CartierModule p Y.F,
          m = MvFormalGroup.CartierModule.endAct Y.varpiEnd x + MvFormalGroup.CartierModule.verschiebungInt x'} :=
    ⟨hinv1, hPiinv, _, hx2, _, hdec2⟩
  obtain ⟨z₀, hz₀, hlz₀⟩ := hB.surjOn ht1
  obtain ⟨z₁, hz₁, hlz₁⟩ := hB.surjOn ht2
  obtain ⟨x₀, x₀', hx₀, hx₀', rfl⟩ := exists_nMk_of_mem_nPiece jR Y hc 1 z₀ (AddSubgroup.mem_inf.mp hz₀).2
  obtain ⟨x₁, x₁', hx₁, hx₁', rfl⟩ := exists_nMk_of_mem_nPiece jR Y hc 1 z₁ (AddSubgroup.mem_inf.mp hz₁).2
  rw [lambda_nMk] at hlz₀ hlz₁
  have hV0 : ∃ g : CartierModule p Y.F, verschiebungInt g = x₀ - WittVector.teichmuller p b • δ 1 := by
    refine hinj _ (Submodule.sub_mem _ hx₀ hx1) ⟨-(g₁ + WittVector.teichmuller p (b ^ p) • δ 1) - x₀', ?_⟩
    have e : endAct Y.varpiEnd x₀ + verschiebungInt x₀' =
        endAct Y.varpiEnd (WittVector.teichmuller p b • δ 1) + verschiebungInt (-(g₁ + WittVector.teichmuller p (b ^ p) • δ 1)) :=
      hlz₀.trans hdec1
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
  have hV1 : ∃ g : CartierModule p Y.F, verschiebungInt g = x₁ - -(WittVector.teichmuller p ξ • (WittVector.teichmuller p b • δ 1)) := by
    refine hinj _ (Submodule.sub_mem _ hx₁ hx2) ⟨(δ 1 + WittVector.teichmuller p (ξ ^ p) • (g₁ + WittVector.teichmuller p (b ^ p) • δ 1)) - x₁', ?_⟩
    have e : endAct Y.varpiEnd x₁ + verschiebungInt x₁' =
        endAct Y.varpiEnd (-(WittVector.teichmuller p ξ • (WittVector.teichmuller p b • δ 1))) +
          verschiebungInt (δ 1 + WittVector.teichmuller p (ξ ^ p) • (g₁ + WittVector.teichmuller p (b ^ p) • δ 1)) :=
      hlz₁.trans hdec2
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
  refine ⟨(Y.toGradedCartierModuleData jR hc).nMk (x₀, x₀'), (Y.toGradedCartierModuleData jR hc).nMk (x₁, x₁'), hz₀, hz₁, ?_, ?_, WittVector.teichmuller p b • δ 1,
    -(WittVector.teichmuller p ξ • (WittVector.teichmuller p b • δ 1)), ?_, ?_, ?_, ?_⟩
  · rw [nVarpi_eq_nMk_lambda, lambda_nMk]; exact congrArg (fun m => (Y.toGradedCartierModuleData jR hc).nMk (m, 0)) hlz₀
  · rw [nVarpi_eq_nMk_lambda, lambda_nMk]; exact congrArg (fun m => (Y.toGradedCartierModuleData jR hc).nMk (m, 0)) hlz₁
  · rw [u_apply_eq_mkQ]
    obtain ⟨g, hg⟩ := hV0
    symm
    exact (Submodule.Quotient.eq _).2 ⟨g, hg⟩
  · rw [u_apply_eq_mkQ]
    obtain ⟨g, hg⟩ := hV1
    symm
    exact (Submodule.Quotient.eq _).2 ⟨g, hg⟩
  · intro k
    rw [map_neg, tangent_smul_witt, tangent_smul_witt, Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    erw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    rw [neg_mul]
  · obtain ⟨k, hk⟩ := exists_tangent_ne_zero jR Y δ hδ 1
    refine ⟨k, ?_⟩
    rw [tangent_smul_witt, Pi.smul_apply, smul_eq_mul]
    erw [WittVector.teichmuller_coeff_zero]
    intro h0
    apply hk
    have : (ξ ^ p - ξ) * (b * tangent (δ 1) k) = 0 := by rw [h0, mul_zero]
    rwa [← mul_assoc, hab, one_mul] at this

end Xi

theorem finish {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] [CharP S p] [Nontrivial S] (g : B →+* S)
    (hcg : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).IsCanonicalLMap L)
    (δ : Fin 2 → CartierModule p (t.XS g).F) (η : S) (hu : IsUnit (η ^ p - η))
    (hδ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) δ)
    (ha : (t.XS g).HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : S) η))
    (v₀ v₁ : Fin 2 → ℚ_[p])
    (hrel0 : ∀ z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod,
      (p : ℕ) • z = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z) →
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nMk (δ 1, 0) →
      Rigidified.LatticeRel ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) t.n (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg)
        (t.etaRed ι ψ g hcg hcb z) v₀)
    (hrel1 : ∀ z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod,
      (p : ℕ) • z = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z) →
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z =
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nMk (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1, 0) →
      Rigidified.LatticeRel ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) t.n (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg)
        (t.etaRed ι ψ g hcg hcb z) v₁) :
    ∃ (z₀ z₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
      (hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD g hcg hcb hcΦg L hL 0 z₀ v₀)
      (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD g hcg hcb hcΦg L hL 0 z₁ v₁)
      (m₀ m₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).M),
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).vRange.mkQ m₀ =
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).vRange.mkQ m₁ =
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
      (∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j = -(η) * MvFormalGroup.CartierModule.tangent m₀ j) ∧
      ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0 := by
  obtain ⟨z₀, z₁, hz₀m, hz₁m, hP0, hP1, m₀, m₁, hm₀, hm₁, htan, hne⟩ :=
    exists_sections_zero (Rigidified.jS ι ψ g) (t.XS g) hcg δ (0 : S) η rfl hu hδ ha L hL
  refine ⟨z₀, z₁,
    (Rigidified.isEtaSection_zero_iff ι hcΦ rΦ ψ t hOD g hcg hcb hcΦg L hL z₀ v₀).2
      ⟨hz₀m, hrel0 z₀ (nsmul_eq_nVarpi_nVarpi (Rigidified.jS ι ψ g) (t.XS g) hcg z₀) hP0⟩,
    (Rigidified.isEtaSection_zero_iff ι hcΦ rΦ ψ t hOD g hcg hcb hcΦg L hL z₁ v₁).2
      ⟨hz₁m, hrel1 z₁ (nsmul_eq_nVarpi_nVarpi (Rigidified.jS ι ψ g) (t.XS g) hcg z₁) hP1⟩,
    m₀, m₁, hm₀, hm₁, htan, hne⟩

section Rel

variable {O : Type} [CommRing O] (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
  (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
  (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
  {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
  (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
  {S : Type} [CommRing S] (g : B →+* S)
  (hcg : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)

theorem etaRed_nMk (x x' : CartierModule p (t.XS g).F) :
    t.etaRed ι ψ g hcg hcb (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nMk (x, x')) =
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (t.redC g x, t.redC g x') := rfl

theorem etaRed_nVarpi_nMk (x : CartierModule p (t.XS g).F) :
    t.etaRed ι ψ g hcg hcb (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi
        (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nMk (x, 0))) =
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nVarpi
        (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (t.redC g x, 0)) := by
  rw [nVarpi_nMk, nVarpi_nMk, etaRed_nMk, map_zero, map_zero]
  show ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (t.redC g (endAct (t.XS g).varpiEnd x), t.redC g 0) = _
  rw [t.redC_endAct_varpiEnd g, map_zero]
  rfl

theorem latticeRel_of_eq_pow_smul_etaRed (a m' e : ℕ) (hn : t.n = m' + 1)
    (w : Fin 2 → ℤ_[p]) (v : Fin 2 → ℚ_[p]) (hv : (p : ℚ_[p]) ^ e • v = fun i => ((w i : ℤ_[p]) : ℚ_[p]))
    (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
    (X : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod)
    (hR : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg w = p ^ (a + m') • X)
    (hX : X = (p ^ (1 + e) : ℕ) • t.etaRed ι ψ g hcg hcb z) :
    Rigidified.LatticeRel ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) t.n
      (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg) (t.etaRed ι ψ g hcg hcb z) v := by
  refine ⟨e, a, w, hv, ?_⟩
  rw [hR, hX, ← mul_smul, ← pow_add, hn]
  congr 2
  omega

theorem nVarpi_nMk_smul_eq_sq_smul_etaRed (δ1 : CartierModule p (t.XS g).F) (δb1 : CartierModule p (t.XbarS g).F)
    (hred1 : t.redC g δ1 = δb1)
    (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
    (hpz : (p : ℕ) • z = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z))
    (hPz : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nMk (δ1, 0)) :
    ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nVarpi
        (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk ((p : WittVector p (S ⧸ pIdeal p S)) • δb1, 0)) =
      (p ^ (1 + 1) : ℕ) • t.etaRed ι ψ g hcg hcb z := by
  rw [pow_add, pow_one, mul_smul, ← map_nsmul, hpz, hPz, etaRed_nVarpi_nMk, hred1, ← map_nsmul, ← map_nsmul,
    Prod.smul_mk, nsmul_zero, Nat.cast_smul_eq_nsmul]
  rfl

theorem nMk_sub_eq_smul_etaRed (δ0 δ1 : CartierModule p (t.XS g).F) (δb0 δb1 : CartierModule p (t.XbarS g).F)
    (η : S) (ηb : S ⧸ pIdeal p S)
    (hredInv : t.redC g (verschiebungInt δ0 - WittVector.teichmuller p η • δ1) = verschiebungInt δb0 - WittVector.teichmuller p ηb • δb1)
    (hPiInvB : endAct (t.XbarS g).varpiEnd (verschiebungInt δb0 - WittVector.teichmuller p ηb • δb1) =
      (p : WittVector p (S ⧸ pIdeal p S)) • δb0 - verschiebungInt (WittVector.teichmuller p (ηb ^ p ^ 2) • δb1))
    (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
    (hpz : (p : ℕ) • z = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z))
    (hPz : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nVarpi z =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).nMk (verschiebungInt δ0 - WittVector.teichmuller p η • δ1, 0)) :
    ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk
        ((p : WittVector p (S ⧸ pIdeal p S)) • δb0 - verschiebungInt (WittVector.teichmuller p (ηb ^ p ^ 2) • δb1), 0) =
      (p ^ (1 + 0) : ℕ) • t.etaRed ι ψ g hcg hcb z := by
  rw [add_zero, pow_one, ← map_nsmul, hpz, hPz, etaRed_nVarpi_nMk, hredInv, nVarpi_nMk, map_zero]
  show _ = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (endAct (t.XbarS g).varpiEnd (verschiebungInt δb0 - WittVector.teichmuller p ηb • δb1), 0)
  rw [hPiInvB]

end Rel

section Finish2

variable {O : Type} [CommRing O] (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
  (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
  (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
  {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
  (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
  {S : Type} [CommRing S] (g : B →+* S)
  (hcg : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)

omit [Algebra ℤ_[p] B] in

theorem redC_verschiebungInt_sub_teichmuller_smul (δ0 δ1 : CartierModule p (t.XS g).F) (η : S) :
    t.redC g (verschiebungInt δ0 - WittVector.teichmuller p η • δ1) =
      verschiebungInt (t.redC g δ0) - WittVector.teichmuller p (Ideal.Quotient.mk (pIdeal p S) η) • t.redC g δ1 := by
  rw [map_sub, t.redC_verschiebungInt g]
  show _ - baseChangeEq _ _ (_ • _) = _
  rw [baseChangeEq_smul_witt, WittVector.map_teichmuller]

omit [Algebra ℤ_[p] B] in

theorem varpi_redInv_eq (δ0 δ1 : CartierModule p (t.XS g).F) (η : S)
    (hPiInv : endAct (t.XS g).varpiEnd (verschiebungInt δ0 - WittVector.teichmuller p η • δ1) =
      (p : WittVector p S) • δ0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ1)) :
    endAct (t.XbarS g).varpiEnd (verschiebungInt (t.redC g δ0) - WittVector.teichmuller p (Ideal.Quotient.mk (pIdeal p S) η) • t.redC g δ1) =
      (p : WittVector p (S ⧸ pIdeal p S)) • t.redC g δ0 -
        verschiebungInt (WittVector.teichmuller p ((Ideal.Quotient.mk (pIdeal p S) η) ^ p ^ 2) • t.redC g δ1) := by
  rw [← redC_verschiebungInt_sub_teichmuller_smul, ← t.redC_endAct_varpiEnd g, hPiInv, map_sub, t.redC_verschiebungInt g]
  show baseChangeEq _ _ (_ • _) - verschiebungInt (baseChangeEq _ _ (_ • _)) = _
  rw [baseChangeEq_smul_witt, baseChangeEq_smul_witt, WittVector.map_teichmuller, map_natCast, map_pow]

variable [CharP S p] [Nontrivial S]

theorem finish_of_rigidNum
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).IsCanonicalLMap L)
    (δ : Fin 2 → CartierModule p (t.XS g).F) (η : S) (hu : IsUnit (η ^ p - η))
    (hδ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) δ)
    (ha : (t.XS g).HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : S) η))
    (a m' : ℕ) (hn : t.n = m' + 1)
    (δb : Fin 2 → CartierModule p (t.XbarS g).F) (hredδ : ∀ i, t.redC g (δ i) = δb i)
    (ηb : S ⧸ pIdeal p S) (hηb : Ideal.Quotient.mk (pIdeal p S) η = ηb)
    (hR0 : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg (Pi.single 0 1) =
      p ^ (a + m') • ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk
        ((p : WittVector p (S ⧸ pIdeal p S)) • δb 0 - verschiebungInt (WittVector.teichmuller p (ηb ^ p ^ 2) • δb 1), 0))
    (hR1 : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg (Pi.single 1 1) =
      p ^ (a + m') • ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nVarpi
        (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk ((p : WittVector p (S ⧸ pIdeal p S)) • δb 1, 0))) :
    ∃ (z₀ z₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).NMod)
      (hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD g hcg hcb hcΦg L hL 0 z₀
        ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD g hcg hcb hcΦg L hL 0 z₁
        ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]))
      (m₀ m₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).M),
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).vRange.mkQ m₀ =
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).vRange.mkQ m₁ =
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hcg).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
      (∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j = -(η) * MvFormalGroup.CartierModule.tangent m₀ j) ∧
      ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0 := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hcoe0 : (p : ℚ_[p]) ^ 1 • ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])) =
      fun i => (((Pi.single 1 1 : Fin 2 → ℤ_[p]) i : ℤ_[p]) : ℚ_[p]) := by
    rw [pow_one, smul_smul, mul_inv_cancel₀ hp, one_smul]
    funext i
    show (Pi.single (1 : Fin 2) (1 : ℚ_[p]) : Fin 2 → ℚ_[p]) i = _
    fin_cases i <;> simp
  have hcoe1 : (p : ℚ_[p]) ^ 0 • ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) =
      fun i => (((Pi.single 0 1 : Fin 2 → ℤ_[p]) i : ℤ_[p]) : ℚ_[p]) := by
    rw [pow_zero, one_smul]
    funext i
    show (Pi.single (0 : Fin 2) (1 : ℚ_[p]) : Fin 2 → ℚ_[p]) i = _
    fin_cases i <;> simp
  have hPiInv : endAct (t.XS g).varpiEnd (verschiebungInt (δ 0) - WittVector.teichmuller p η • δ 1) =
      (p : WittVector p S) • δ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1) :=
    K82Edge.pi_etaInv_eq_natCast_smul_sub (Rigidified.jS ι ψ g) (0 : S) η (t.XS g) δ rfl hδ ha
  have hPiInvB := varpi_redInv_eq Φ t g (δ 0) (δ 1) η hPiInv
  have hredInv := redC_verschiebungInt_sub_teichmuller_smul Φ t g (δ 0) (δ 1) η
  rw [hredδ 0, hredδ 1, hηb] at hPiInvB hredInv
  refine finish ι Φ hcΦ rΦ ψ t hOD g hcg hcb hcΦg L hL δ η hu hδ ha _ _ ?_ ?_
  · intro z hpz hPz
    exact latticeRel_of_eq_pow_smul_etaRed ι Φ hcΦ rΦ ψ t hOD g hcg hcb hcΦg a m' 1 hn (Pi.single 1 1) _ hcoe0 z _ hR1
      (nVarpi_nMk_smul_eq_sq_smul_etaRed ι Φ ψ t g hcg hcb (δ 1) (δb 1) (hredδ 1) z hpz hPz)
  · intro z hpz hPz
    exact latticeRel_of_eq_pow_smul_etaRed ι Φ hcΦ rΦ ψ t hOD g hcg hcb hcΦg a m' 0 hn (Pi.single 0 1) _ hcoe1 z _ hR0
      (nMk_sub_eq_smul_etaRed ι Φ ψ t g hcg hcb (δ 0) (δ 1) (δb 0) (δb 1) η ηb hredInv hPiInvB z hpz hPz)

end Finish2

end K83Sec0

namespace K82EtaN

open CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

theorem bc3_smul_sub {p : ℕ} [Fact p.Prime]
    {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (Y : FormalODModule p R₀) (δ : Fin 2 → CartierModule p Y.F) (i j : Fin 2) (x : R₀)
    (f₁ : R₀ →+* R₁) (f₂ : R₁ →+* R₂) (f₃ : R₂ →+* R₃) :
    baseChange f₃ (baseChange f₂ (baseChange f₁
        ((p : WittVector p R₀) • δ i - verschiebungInt (WittVector.teichmuller p (x ^ p ^ 2) • δ j)))) =
      (p : WittVector p R₃) • baseChange f₃ (baseChange f₂ (baseChange f₁ (δ i))) -
        verschiebungInt (WittVector.teichmuller p ((f₃ (f₂ (f₁ x))) ^ p ^ 2) •
          baseChange f₃ (baseChange f₂ (baseChange f₁ (δ j)))) := by
  simp only [map_sub, MvFormalGroup.CartierModule.baseChange, MvFormalGroup.CartierModule.baseChangeEq_smul_witt,
    MvFormalGroup.CartierModule.baseChangeEq_verschiebungInt, map_natCast, WittVector.map_teichmuller, map_pow]

theorem bc3_smul_sub_of_eq_zero {p : ℕ} [Fact p.Prime]
    {R₀ R₁ R₂ R₃ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (Y : FormalODModule p R₀) (δ : Fin 2 → CartierModule p Y.F) (i j : Fin 2) (x : R₀)
    (f₁ : R₀ →+* R₁) (f₂ : R₁ →+* R₂) (f₃ : R₂ →+* R₃) (hx : f₁ x = 0) :
    baseChange f₃ (baseChange f₂ (baseChange f₁
        ((p : WittVector p R₀) • δ i - verschiebungInt (WittVector.teichmuller p (x ^ p ^ 2) • δ j)))) =
      (p : WittVector p R₃) • baseChange f₃ (baseChange f₂ (baseChange f₁ (δ i))) := by
  rw [bc3_smul_sub, hx, map_zero, map_zero, zero_pow (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero),
    WittVector.teichmuller_zero, zero_smul, map_zero, sub_zero]

theorem xiSec1Package (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] [CharP S p] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (δ : Fin 2 → CartierModule p (t.XS g).F) (c : S)
    (hcore : ∃ (z₀ z₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
      (hz₀ : z₀ ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).etaPiece L hL.isCartierLMap.map_verschiebung 1)
      (hz₁ : z₁ ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).etaPiece L hL.isCartierLMap.map_verschiebung 1),
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi z₀ = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMk (δ 0, 0) ∧
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi z₁ = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMk (verschiebungInt (δ 1) - WittVector.teichmuller p c • δ 0, 0) ∧
      ∃ (m₀ m₁ : CartierModule p (t.XS g).F),
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).vRange.mkQ m₀ = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀).1⟩ ∧
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).vRange.mkQ m₁ = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁).1⟩ ∧
        (∀ k : Fin 2, tangent m₁ k = -c * tangent m₀ k) ∧
        ∃ k : Fin 2, tangent m₀ k ≠ 0)
    (mb₀ mb₁ : CartierModule p (t.XbarS g).F)
    (hred₀ : t.redC g (δ 0) = mb₀) (hred₁ : t.redC g (δ 1) = mb₁)
    (hBz : endAct (t.XbarS g).varpiEnd
        (verschiebungInt mb₁ - WittVector.teichmuller p (Ideal.Quotient.mk (pIdeal p S) c) • mb₀) =
      (p : WittVector p (S ⧸ pIdeal p S)) • mb₁ -
        verschiebungInt (WittVector.teichmuller p ((Ideal.Quotient.mk (pIdeal p S) c) ^ p ^ 2) • mb₀))
    (a n₀ : ℕ) (hn : t.n = n₀ + 1)
    (hr0 : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg (Pi.single 0 1) =
      p ^ (a + n₀) • ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (((p : WittVector p (S ⧸ pIdeal p S)) • mb₀ : CartierModule p (t.XbarS g).F), 0))
    (hr1 : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg (Pi.single 1 1) =
      p ^ (a + n₀) • ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nVarpi (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk
        (((p : WittVector p (S ⧸ pIdeal p S)) • mb₁ -
          verschiebungInt (WittVector.teichmuller p ((Ideal.Quotient.mk (pIdeal p S) c) ^ p ^ 2) • mb₀) : CartierModule p (t.XbarS g).F), 0))) :
    ∃ (hOD' : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
      (hc' : t.IsGradedS ι ψ g) (hcb' : t.IsGradedSbar ι ψ g) (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
      (L' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').M →+
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').NMod)
      (hL' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').IsCanonicalLMap L')
      (z₀ z₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').NMod)
      (hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD' g hc' hcb' hcΦg' L' hL' 1 z₀ ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD' g hc' hcb' hcΦg' L' hL' 1 z₁ ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (m₀ m₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').M),
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').vRange.mkQ m₀ =
          ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').u L' hL'.isCartierLMap.map_verschiebung
            ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').vRange.mkQ m₁ =
          ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').u L' hL'.isCartierLMap.map_verschiebung
            ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
        (∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j = -c * MvFormalGroup.CartierModule.tangent m₀ j) ∧
        ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0 := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp0
  obtain ⟨z₀, z₁, hz₀, hz₁, hPz₀, hPz₁, m₀, m₁, hmk₀, hmk₁, htan, hne⟩ := hcore

  have hvarpiB : ∀ u : CartierModule p (t.XbarS g).F, ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nVarpi (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (u, 0)) = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (endAct (t.XbarS g).varpiEnd u, 0) := by
    intro u
    show ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).varpi u, ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).varpi 0) = _
    rw [map_zero]
    try rfl
  have hetaRed0 : ∀ z : CartierModule p (t.XS g).F,
      t.etaRed ι ψ g hc hcb (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMk (z, 0)) = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (t.redC g z, 0) := by
    intro z
    refine (GradedCartierModuleData.nMap_nMk ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g)
      (t.redC_endAct_varpiEnd g) z 0).trans ?_
    rw [map_zero]
    try rfl
  have hnatB : ∀ u : CartierModule p (t.XbarS g).F, ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (((p : WittVector p (S ⧸ pIdeal p S)) • u : CartierModule p (t.XbarS g).F), 0) = p • ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (u, 0) := by
    intro u
    rw [← map_nsmul, Prod.smul_mk, smul_zero, Nat.cast_smul_eq_nsmul]
    try rfl
  have hnatB' : ∀ u : CartierModule p (t.XbarS g).F, ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk ((p • u : CartierModule p (t.XbarS g).F), 0) = p • ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (u, 0) := by
    intro u
    rw [← map_nsmul, Prod.smul_mk, smul_zero]
    try rfl
  have hredz : t.redC g (verschiebungInt (δ 1) - WittVector.teichmuller p c • δ 0) =
      verschiebungInt mb₁ - WittVector.teichmuller p (Ideal.Quotient.mk (pIdeal p S) c) • mb₀ := by
    rw [map_sub, Rigidified.redC_verschiebungInt, hred₁]
    congr 1
    have h1 := MvFormalGroup.CartierModule.baseChangeEq_smul_witt (p := p)
      (Ideal.Quotient.mk (pIdeal p S)) (t.XS_F_map_mk g) (WittVector.teichmuller p c) (δ 0)
    rw [WittVector.map_teichmuller] at h1
    exact h1.trans (congrArg _ hred₀)

  have hrel0 : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg (Pi.single 0 1) =
      p ^ (a + t.n + 0) • t.etaRed ι ψ g hc hcb (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi z₀) := by
    rw [hPz₀, hetaRed0, hred₀, hn, add_zero, ← add_assoc, pow_succ, mul_smul, ← hnatB, hr0]
  have hrel1 : p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg (Pi.single 1 1) =
      p ^ (a + t.n + 0) • t.etaRed ι ψ g hc hcb (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi z₁) := by
    rw [hPz₁, hetaRed0, hredz, hn, add_zero, ← add_assoc, pow_succ, mul_smul, ← hnatB', hr1, hvarpiB, ← hBz,
      CerednikDrinfeld.FormalODModule.endAct_varpiEnd_endAct_varpiEnd]

  have hcoe : ∀ i : Fin 2, (p : ℚ_[p]) ^ 0 • ((p : ℚ_[p]) • ((p : ℚ_[p])⁻¹ •
      ((stdBasisVec ℚ_[p] i : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]))) =
      fun l => (((Pi.single i 1 : Fin 2 → ℤ_[p]) l : ℤ_[p]) : ℚ_[p]) := by
    intro i
    rw [pow_zero, one_smul, smul_inv_smul₀ hpQ]
    funext l
    by_cases h : l = i
    · subst h; simp [stdBasisVec]
    · simp [stdBasisVec, Pi.single_apply, h]
  have hsec₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL 1 z₀ ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])) := by
    rw [Rigidified.isEtaSection_one_iff]
    exact ⟨hz₀, 0, a, Pi.single 0 1, hcoe 0, hrel0⟩
  have hsec₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL 1 z₁ ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])) := by
    rw [Rigidified.isEtaSection_one_iff]
    exact ⟨hz₁, 0, a, Pi.single 1 1, hcoe 1, hrel1⟩
  exact ⟨hOD, hc, hcb, hcΦg, L, hL, z₀, z₁, hsec₀, hsec₁, m₀, m₁, hmk₀, hmk₁, htan, hne⟩

end K82EtaN

set_option maxHeartbeats 8000000 in
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
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ≠ 0) :
    ∃ (hOD : FormalODModule.IsODHom (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).Φbar (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).Xbar ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).ρ)
      (hc : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsGradedS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (hcb : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsGradedSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (L : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).M →+ ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hL : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).IsCanonicalLMap L)
      (z₀ z₁ : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hz₀ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsEtaSection ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 z₀
        ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (hz₁ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsEtaSection ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 z₁
        ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (m₀ m₁ : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).M),
      ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₀ = ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
      ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₁ = ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
      (∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j =
        -(Rigidified.awayHom (1 : Ω) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) * MvFormalGroup.CartierModule.tangent m₀ j) ∧
      ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0 := by
  classical

  have hpk : ((p : ℕ) : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hpE : ((p : ℕ) : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = 0 := by rw [← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))), hpk, map_zero]
  have hpΩ : ((p : ℕ) : Ω) = 0 := by rw [← map_natCast y, hpE, map_zero]
  haveI hcharΩ : CharP Ω p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ
  have hnil : IsNilpotent ((p : ℕ) : Ω) := ⟨1, by rw [pow_one, hpΩ]⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have hyη : y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    have h := congrArg y (EdgeFamily.edgeRingCharP.ξ_mul_η p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    rw [map_mul, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hyξ
  have hξpow : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ≠ y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) := by
    have hu := (FormalOmega.chartERing.isUnit_discr (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : WittVector p k ⧸ pIdeal p (WittVector p k)) p).map y
    rw [map_mul, map_sub, map_pow, map_one, map_sub, map_pow, map_one] at hu
    have hne : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ (p - 1) - 1 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hu; exact not_isUnit_zero hu
    intro heq
    apply hne
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
    have h2 : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ (p - 1) * y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 1 * y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) := by
      rw [← pow_succ, hp1, heq, one_mul]
    rw [mul_right_cancel₀ hyξ h2, sub_self]
  have hξu : IsUnit (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p - y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) := isUnit_iff_ne_zero.2 (sub_ne_zero.2 hξpow)

  haveI : IsNoetherianRing (FormalOmega.edgeQuot (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : WittVector p k ⧸ pIdeal p (WittVector p k))) :=
    show IsNoetherianRing (MvPolynomial (Fin 2) (WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ Ideal.span {FormalOmega.edgeRel (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : WittVector p k ⧸ pIdeal p (WittVector p k))}) from
      inferInstance
  haveI : IsNoetherianRing (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) := inferInstance
  have hadmE := CerednikDrinfeld.SpecialFormal.Rigidified.isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
    p k ι Φ X hXs hX4 f₀ m ρ₀ hρ₀ ρ₁.toSeries hρ₁h
  have hadm := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ y _ hadmE
  have hODt : FormalODModule.IsODHom (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).Φbar (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).Xbar ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).ρ := hadm.2.2.1

  have hJ : y.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) = (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) := rfl
  have hγΩ : (X.map y).IsHomogeneousVBasis (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (fun i => (baseChange y (γ i))) :=
    K82Edge.isHomogeneousVBasis_map_of_eq y hγ hJ
  have hγaΩ : (X.map y).HasStructureConstants (fun i => (baseChange y (γ i))) (EdgeFamily.edgeConstants p (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (0 : Ω)) := by
    have h := K82Edge.hasStructureConstants_map_edgeConstants y X γ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) hγa
    rw [hyη] at h
    exact h

  have hgr := Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hnil ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) (1 : Ω)
  have hcS := hgr.1
  have hcbS := hgr.2.1
  have hcΦS := hgr.2.2

  have hR := CerednikDrinfeld.FormalODModule.smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h
    Ω y (Rigidified.awayHom (1 : Ω)) hODt hcbS hcΦS

  have hinjA : Function.Injective (algebraMap Ω (Rigidified.Baway (1 : Ω))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors one_ne_zero)
  haveI hcharB : CharP (Rigidified.Baway (1 : Ω)) p := charP_of_injective_algebraMap hinjA p
  have hpB : ((p : ℕ) : (Rigidified.Baway (1 : Ω))) = 0 := CharP.cast_eq_zero _ _
  have hsep : IsHausdorff (Ideal.span {((p : ℕ) : (Rigidified.Baway (1 : Ω)))}) (Rigidified.Baway (1 : Ω)) := by
    rw [hpB, Ideal.span_singleton_eq_bot.2 rfl]
    infer_instance
  have hpI : pIdeal p (Rigidified.Baway (1 : Ω)) = ⊥ := by
    rw [pIdeal, hpB, Ideal.span_singleton_eq_bot]
  haveI hntS : Nontrivial (Rigidified.Baway (1 : Ω)) := hinjA.nontrivial
  haveI hntSB : Nontrivial ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω))) := Ideal.Quotient.nontrivial_iff.mpr (by rw [hpI]; exact bot_ne_top)
  haveI hcharSB : CharP ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω))) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))), hpB, map_zero])
  have hcbar : (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) = (reduceMap (Rigidified.awayHom (1 : Ω)) (Ideal.Quotient.mk (pIdeal p Ω) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) := by
    rw [reduceMap, residueMap, Ideal.quotientMap_mk]
  have hcu : IsUnit (((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) ^ p - ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) := by
    have h := hξu.map (Rigidified.awayHom (1 : Ω))
    rw [map_sub, map_pow] at h
    exact h

  have hγS : (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).IsHomogeneousVBasis (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (fun i => (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i)))) := hγΩ.map (Rigidified.awayHom (1 : Ω))
  have hLex :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hsep (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))) (fun i => (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i)))) hγS hcS
  have hγaS : (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).HasStructureConstants (fun i => (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i)))) (EdgeFamily.edgeConstants p ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (0 : (Rigidified.Baway (1 : Ω)))) := by
    have h := K82Edge.hasStructureConstants_map_edgeConstants (Rigidified.awayHom (1 : Ω)) (X.map y) (fun i => (baseChange y (γ i))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (0 : Ω) hγaΩ
    rw [map_zero] at h
    exact h
  have hγB : (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).IsHomogeneousVBasis (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (fun i => (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ i))))) :=
    (hγΩ.map (Ideal.Quotient.mk (pIdeal p Ω))).map (reduceMap (Rigidified.awayHom (1 : Ω)))
  have hγaB : (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).HasStructureConstants (fun i => (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ i))))) (EdgeFamily.edgeConstants p (reduceMap (Rigidified.awayHom (1 : Ω)) (Ideal.Quotient.mk (pIdeal p Ω) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (0 : ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω))))) := by
    have h1 := K82Edge.hasStructureConstants_map_edgeConstants (Ideal.Quotient.mk (pIdeal p Ω)) (X.map y) (fun i => (baseChange y (γ i))) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (0 : Ω) hγaΩ
    rw [map_zero] at h1
    have h2 := K82Edge.hasStructureConstants_map_edgeConstants (reduceMap (Rigidified.awayHom (1 : Ω))) _ _ _ (0 : Ω ⧸ pIdeal p Ω) h1
    rw [map_zero] at h2
    exact h2

  have hred : ∀ i : Fin 2, ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).redC (Rigidified.awayHom (1 : Ω)) (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i))) = (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ i)))) := by
    intro i
    refine MvFormalGroup.CartierModule.ext (funext fun j => ?_)
    simp only [Rigidified.redC, MvFormalGroup.CartierModule.baseChange,
      MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq]
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map]
    rfl
  have hPiBz : endAct (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).varpiEnd
      (verschiebungInt (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 1)))) - WittVector.teichmuller p (reduceMap (Rigidified.awayHom (1 : Ω)) (Ideal.Quotient.mk (pIdeal p Ω) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0))))) =
      (p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 1)))) - verschiebungInt (WittVector.teichmuller p ((reduceMap (Rigidified.awayHom (1 : Ω)) (Ideal.Quotient.mk (pIdeal p Ω) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0))))) :=
    K82Edge.pi_xiInv_eq_natCast_smul_sub (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (reduceMap (Rigidified.awayHom (1 : Ω)) (Ideal.Quotient.mk (pIdeal p Ω) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (0 : ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))) (fun i => (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ i))))) rfl hγB hγaB
  have hPiBz' : endAct (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).varpiEnd
      (verschiebungInt (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 1)))) - WittVector.teichmuller p ((Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0))))) =
      (p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 1)))) - verschiebungInt (WittVector.teichmuller p (((Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0))))) := by
    rw [hcbar]
    exact hPiBz

  have hr0 : p ^ a • ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).rigidNum ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hODt (Rigidified.awayHom (1 : Ω)) hcbS hcΦS (Pi.single 0 1) =
      p ^ (a + m) • ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0)))) : CartierModule p (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).F), 0) :=
    (hR 0).trans (congrArg (fun w : CartierModule p (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).F => p ^ (a + m) • ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (w, 0))
      (K82EtaN.bc3_smul_sub_of_eq_zero X γ 0 1 (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) y (Ideal.Quotient.mk (pIdeal p Ω)) (reduceMap (Rigidified.awayHom (1 : Ω))) hyη))
  have hr1 : p ^ a • ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).rigidNum ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hODt (Rigidified.awayHom (1 : Ω)) hcbS hcΦS (Pi.single 1 1) =
      p ^ (a + m) • ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 1)))) -
        verschiebungInt (WittVector.teichmuller p (((Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) ^ p ^ 2) • (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0))))) : CartierModule p (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).F), 0)) := by
    rw [hcbar]
    exact (hR 1).trans (congrArg (fun w : CartierModule p (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).F => p ^ (a + m) • ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nVarpi (((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcbS).nMk (w, 0)))
      (K82EtaN.bc3_smul_sub X γ 1 0 (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) y (Ideal.Quotient.mk (pIdeal p Ω)) (reduceMap (Rigidified.awayHom (1 : Ω)))))

  have hcore := K83Sec0.exists_sections_one (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))) hcS (fun i => (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (0 : (Rigidified.Baway (1 : Ω))) rfl hcu hγS hγaS
    hLex.choose hLex.choose_spec
  exact K82EtaN.xiSec1Package p ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) hODt (Rigidified.awayHom (1 : Ω)) hcS hcbS hcΦS hLex.choose hLex.choose_spec
    (fun i => (baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i)))) ((Rigidified.awayHom (1 : Ω)) (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))))) hcore (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 0)))) (baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ 1)))) (hred 0) (hred 1) hPiBz' a m rfl hr0 hr1

end
end S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_ne_zero (solution)
