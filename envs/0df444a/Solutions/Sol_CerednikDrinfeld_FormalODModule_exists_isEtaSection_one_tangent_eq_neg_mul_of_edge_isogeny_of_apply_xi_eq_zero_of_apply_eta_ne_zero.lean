-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f3e6b064-2ef7-519e-b39f-55fd810f1fa8

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_one_of_lieOne_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero
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

namespace K86

p2m_open "CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData"

theorem redC_smul_witt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B S : Type} [CommRing B] [CommRing S] (t : Rigidified p Φ B) (g : B →+* S)
    (w : WittVector p S) (m : CartierModule p (t.XS g).F) :
    t.redC g (w • m) = WittVector.map (Ideal.Quotient.mk (pIdeal p S)) w • t.redC g m :=
  baseChangeEq_smul_witt _ _ w m

theorem redC_sub {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B S : Type} [CommRing B] [CommRing S] (t : Rigidified p Φ B) (g : B →+* S)
    (m m' : CartierModule p (t.XS g).F) :
    t.redC g (m - m') = t.redC g m - t.redC g m' :=
  map_sub _ _ _

private theorem _root_.K86.isNoetherianRing_edgeRingCharP {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (EdgeFamily.edgeRingCharP p R) := by
  haveI : IsNoetherianRing (FormalOmega.edgeQuot R (0 : R)) :=
    show IsNoetherianRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {FormalOmega.edgeRel R (0:R)}) from inferInstance
  exact IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr R (0:R) p)) _ inferInstance

p2m_export "K86" "isNoetherianRing_edgeRingCharP"

theorem k85_nsmul_helper {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime] (r : (Fin 2 → ℤ_[p]) →+ M)
    (a N : ℕ) (A : M) (h : p ^ a • r (Pi.single 0 1) = p ^ (a + N) • A) :
    p ^ a • r (p • (Pi.single 0 1 : Fin 2 → ℤ_[p])) = p ^ (a + N + 1) • A := by
  rw [map_nsmul, smul_comm, h, smul_smul, ← pow_succ']

set_option maxHeartbeats 1600000 in

theorem etaSec1
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (Ω : Type) [Field Ω] [CharP Ω p] [Algebra ℤ_[p] Ω] (ψ : WittVector p k →+* Ω)
    (t : Rigidified p Φ Ω) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (δ : Fin 2 → CartierModule p t.X.F) (hδ : t.X.IsHomogeneousVBasis (structureMap ι ψ) δ)
    (c : Ω) (ha : t.X.HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : Ω) c))
    (a n : ℕ) (hn : t.n = n + 1)
    (δA : Fin 2 → CartierModule p (t.XS (Rigidified.awayHom (1 : Ω))).F) (hδAdef : ∀ i : Fin 2, δA i = baseChange (Rigidified.awayHom (1 : Ω)) (δ i))
    (δbar : Fin 2 → CartierModule p (t.XbarS (Rigidified.awayHom (1 : Ω))).F)
    (hδbar : ∀ i : Fin 2, t.redC (Rigidified.awayHom (1 : Ω)) (δA i) = δbar i)
    (cbar : (Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))
    (hcbar : (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))) ((Rigidified.awayHom (1 : Ω)) c) = cbar)
    (hR0 : ∀ (hcb' : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : Ω))) (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : Ω))),
      p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hcb' hcΦg' (Pi.single 0 1) =
        p ^ (a + n) • ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb').nMk ((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • δbar 0 -
          verschiebungInt (WittVector.teichmuller p (cbar ^ p ^ 2) • δbar 1), 0))
    (hR1 : ∀ (hcb' : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : Ω))) (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : Ω))),
      p ^ a • t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hcb' hcΦg' (Pi.single 1 1) =
        p ^ (a + n) • ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb').nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb').nMk ((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • δbar 1, 0))) :
    ∃ (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : Ω))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : Ω)))
      (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : Ω)))
      (L : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).NMod) (hL : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).IsCanonicalLMap L)
      (z₀ z₁ : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 z₀ ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 z₁ ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]))
      (m₀ m₁ : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).M),
      ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₀ = ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
      ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₁ = ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
      (∀ j : Fin 2, tangent m₁ j = -((Rigidified.awayHom (1 : Ω)) c) * tangent m₀ j) ∧
      ∃ j : Fin 2, tangent m₀ j ≠ 0 := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hpΩ : ((p : ℕ) : Ω) = 0 := CharP.cast_eq_zero Ω p
  have hnil : IsNilpotent ((p : ℕ) : Ω) := ⟨1, by rw [pow_one, hpΩ]⟩
  obtain ⟨hc, hcb, hcΦg⟩ :=
    Rigidified.isGradedS_and_isGradedSbar_and_isGradedPhiS_awayHom ι ψ hnil t (1 : Ω)

  have hinjA : Function.Injective (algebraMap Ω (Rigidified.Baway (1 : Ω))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors one_ne_zero)
  haveI hcharB : CharP (Rigidified.Baway (1 : Ω)) p := charP_of_injective_algebraMap hinjA p
  haveI hntB : Nontrivial (Rigidified.Baway (1 : Ω)) := hinjA.nontrivial
  have hpB : ((p : ℕ) : (Rigidified.Baway (1 : Ω))) = 0 := CharP.cast_eq_zero _ _
  have hnilB : IsNilpotent ((p : ℕ) : (Rigidified.Baway (1 : Ω))) := ⟨1, by rw [pow_one, hpB]⟩
  have hsep : IsHausdorff (Ideal.span {((p : ℕ) : (Rigidified.Baway (1 : Ω)))}) (Rigidified.Baway (1 : Ω)) := by
    rw [hpB, Ideal.span_singleton_eq_bot.2 rfl]
    infer_instance

  have hδAeq : (fun i => baseChange (Rigidified.awayHom (1 : Ω)) (δ i)) = δA := funext fun i => (hδAdef i).symm
  have hδA : (t.XS (Rigidified.awayHom (1 : Ω))).IsHomogeneousVBasis (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) δA := by
    have h := hδ.map (Rigidified.awayHom (1 : Ω))
    rw [hδAeq] at h
    exact h
  have haA : (t.XS (Rigidified.awayHom (1 : Ω))).HasStructureConstants δA (EdgeFamily.edgeConstants p (0 : (Rigidified.Baway (1 : Ω))) ((Rigidified.awayHom (1 : Ω)) c)) := by
    have h := K82Edge.hasStructureConstants_map_edgeConstants (Rigidified.awayHom (1 : Ω)) t.X δ 0 c ha
    rw [map_zero, hδAeq] at h
    exact h

  obtain ⟨-, -, -, hLieC⟩ :=
    FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p (structureMap ι ψ) hnil t.X δ hδ
  have hlv1 : t.X.lieOne (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi :=
    K82Edge.lieOne_le_ker_lieVarpi_of_left_eq_zero t.X (structureMap ι ψ) (0 : Ω) c δ rfl hnil hLieC hδ ha
  have hcrit1 := FormalODModule.CritChart.isCritical_map_one_of_lieOne_le_ker_lieVarpi p (structureMap ι ψ) t.X hLieC hlv1 (Rigidified.awayHom (1 : Ω))
  have hi1 : ∀ m' ∈ (t.XS (Rigidified.awayHom (1 : Ω))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) 1, ∃ g' : CartierModule p (t.XS (Rigidified.awayHom (1 : Ω))).F,
      verschiebungInt g' = endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd m' := by
    intro m' hm'
    obtain ⟨g', hg'⟩ := hcrit1 m' hm'
    exact ⟨g', by rw [verschiebungInt_eq_verschiebung]; exact hg'⟩

  obtain ⟨L, hL⟩ :=
    FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hsep (t.XS (Rigidified.awayHom (1 : Ω))) δA hδA hc

  have hPi1 : endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd (δA 1) = verschiebungInt (δA 1) :=
    K82Edge.pi_one_eq_verschiebungInt_of_left_eq_zero (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) (0 : (Rigidified.Baway (1 : Ω))) ((Rigidified.awayHom (1 : Ω)) c) (t.XS (Rigidified.awayHom (1 : Ω))) δA rfl hδA haA
  have hPiW : endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)) = verschiebungInt (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)) :=
    K82Edge.pi_eq_verschiebungInt_etaInv (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) (0 : (Rigidified.Baway (1 : Ω))) ((Rigidified.awayHom (1 : Ω)) c) (t.XS (Rigidified.awayHom (1 : Ω))) δA rfl hδA haA
  have hPiW' : endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)) =
      (p : WittVector p (Rigidified.Baway (1 : Ω))) • (δA 0) - verschiebungInt (WittVector.teichmuller p (((Rigidified.awayHom (1 : Ω)) c) ^ p ^ 2) • (δA 1)) :=
    K82Edge.pi_etaInv_eq_natCast_smul_sub (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) (0 : (Rigidified.Baway (1 : Ω))) ((Rigidified.awayHom (1 : Ω)) c) (t.XS (Rigidified.awayHom (1 : Ω))) δA rfl hδA haA

  have hmem1 : (δA 1) ∈ (t.XS (Rigidified.awayHom (1 : Ω))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) 1 := hδA.1 1
  have hmemW : (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)) ∈ (t.XS (Rigidified.awayHom (1 : Ω))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) 1 :=
    ((t.XS (Rigidified.awayHom (1 : Ω))).gradedPiece (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) 1).sub_mem
      (FormalODModule.verschiebungInt_mem_gradedPiece_succ (t.XS (Rigidified.awayHom (1 : Ω))) (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) 0 _ (hδA.1 0))
      (FormalODModule.smul_mem_gradedPiece (t.XS (Rigidified.awayHom (1 : Ω))) (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) 1 _ _ (hδA.1 1))

  have hL1 : L (δA 1) = ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((δA 1), 0) :=
    FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) (t.XS (Rigidified.awayHom (1 : Ω))) hc L hL 1 hi1 _ _ hmem1 hPi1.symm
  have hLW : L (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)) = ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0) :=
    FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) (t.XS (Rigidified.awayHom (1 : Ω))) hc L hL 1 hi1 _ _ hmemW hPiW.symm
  have hnMk0 : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk (0, 0) = 0 := map_zero _

  have hη1 : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((δA 1), 0) ∈ ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).etaPiece L hL.isCartierLMap.map_verschiebung 1 := by
    refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk, hL1, hnMk0, add_zero]
    · exact AddSubgroup.mem_map.2 ⟨((δA 1), 0), AddSubgroup.mem_prod.2 ⟨hmem1, zero_mem _⟩, rfl⟩
  have hηW : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0) ∈ ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).etaPiece L hL.isCartierLMap.map_verschiebung 1 := by
    refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.phi_nMk, hLW, hnMk0, add_zero]
    · exact AddSubgroup.mem_map.2 ⟨((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0), AddSubgroup.mem_prod.2 ⟨hmemW, zero_mem _⟩, rfl⟩

  have hnVarpi : ∀ m₁ m₂ : ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).M, ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nVarpi (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk (m₁, m₂)) =
      ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).varpi m₁, ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).varpi m₂) := fun _ _ => rfl
  have hnVarpiB : ∀ m₁ m₂ : ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).M, ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (m₁, m₂)) =
      ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).varpi m₁, ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).varpi m₂) := fun _ _ => rfl

  have hred0 : t.etaRed ι ψ (Rigidified.awayHom (1 : Ω)) hc hcb (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nVarpi (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((δA 1), 0))) =
      ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (δbar 1, 0)) := by
    rw [hnVarpi, hnVarpiB, map_zero, map_zero]
    show ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMap ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb) (t.redC (Rigidified.awayHom (1 : Ω))) (t.redC_verschiebungInt (Rigidified.awayHom (1 : Ω))) (t.redC_endAct_varpiEnd (Rigidified.awayHom (1 : Ω))) (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk (endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd (δA 1), 0)) = ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (endAct (t.XbarS (Rigidified.awayHom (1 : Ω))).varpiEnd (δbar 1), 0)
    erw [GradedCartierModuleData.nMap_nMk, map_zero, Rigidified.redC_endAct_varpiEnd, hδbar 1]

  have hredW : t.redC (Rigidified.awayHom (1 : Ω)) (endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1))) =
      (p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • δbar 0 -
        verschiebungInt (WittVector.teichmuller p (cbar ^ p ^ 2) • δbar 1) := by
    rw [hPiW', K86.redC_sub, Rigidified.redC_verschiebungInt, K86.redC_smul_witt, K86.redC_smul_witt, hδbar 0, hδbar 1,
      map_natCast, WittVector.map_teichmuller, map_pow (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : Ω)))), hcbar]
  have hred1 : t.etaRed ι ψ (Rigidified.awayHom (1 : Ω)) hc hcb (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nVarpi (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0))) =
      ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk ((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • δbar 0 -
        verschiebungInt (WittVector.teichmuller p (cbar ^ p ^ 2) • δbar 1), 0) := by
    rw [hnVarpi, map_zero]
    show ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMap ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb) (t.redC (Rigidified.awayHom (1 : Ω))) (t.redC_verschiebungInt (Rigidified.awayHom (1 : Ω))) (t.redC_endAct_varpiEnd (Rigidified.awayHom (1 : Ω))) (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk (endAct (t.XS (Rigidified.awayHom (1 : Ω))).varpiEnd (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0)) = _
    erw [GradedCartierModuleData.nMap_nMk, map_zero, hredW]

  have hpsm : ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk ((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • δbar 1, 0)) =
      p • ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (δbar 1, 0)) := by
    calc ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk ((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • δbar 1, 0))
        = ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi ((p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (δbar 1, 0)) := by
          rw [GradedCartierModuleData.smul_nMk, smul_zero]; try rfl
      _ = (p : WittVector p ((Rigidified.Baway (1 : Ω)) ⧸ pIdeal p (Rigidified.Baway (1 : Ω)))) • ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (δbar 1, 0)) := map_smul _ _ _
      _ = p • ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nVarpi (((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb).nMk (δbar 1, 0)) := by rw [Nat.cast_smul_eq_nsmul]

  have hcoe0 : (p : ℚ_[p]) ^ 0 • ((p : ℚ_[p]) • ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]))) = fun i => ((Pi.single 1 1 : Fin 2 → ℤ_[p]) i : ℚ_[p]) := by
    rw [pow_zero, one_smul]
    show (p : ℚ_[p]) • ((p : ℚ_[p])⁻¹ • (Pi.single 1 1 : Fin 2 → ℚ_[p])) = _
    rw [smul_inv_smul₀ hpQ]
    funext i
    by_cases h : i = 1
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcoe1 : (p : ℚ_[p]) ^ 0 • ((p : ℚ_[p]) • ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])) = fun i => ((p • (Pi.single 0 1 : Fin 2 → ℤ_[p])) i : ℚ_[p]) := by
    rw [pow_zero, one_smul]
    show (p : ℚ_[p]) • (Pi.single 0 1 : Fin 2 → ℚ_[p]) = _
    funext i
    by_cases h : i = 0
    · subst h; simp
    · simp [Pi.single_apply, h]

  have hrel0 : Rigidified.LatticeRel ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb) t.n (t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hcb hcΦg)
      (t.etaRed ι ψ (Rigidified.awayHom (1 : Ω)) hc hcb (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nVarpi (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((δA 1), 0)))) ((p : ℚ_[p]) • ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]))) := by
    have hexp : a + t.n + 0 = a + n + 1 := by rw [hn]; omega
    refine ⟨0, a, Pi.single 1 1, hcoe0, ?_⟩
    rw [hR1 hcb hcΦg, hred0, hpsm, smul_smul, ← pow_succ, hexp]
  have hrel1 : Rigidified.LatticeRel ((t.XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : Ω))) hcb) t.n (t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hcb hcΦg)
      (t.etaRed ι ψ (Rigidified.awayHom (1 : Ω)) hc hcb (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nVarpi (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0)))) ((p : ℚ_[p]) • ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])) := by
    have hexp : a + t.n + 0 = a + n + 1 := by rw [hn]; omega
    refine ⟨0, a, p • Pi.single 0 1, hcoe1, ?_⟩
    rw [hexp, hred1]
    exact K86.k85_nsmul_helper _ a n _ (hR0 hcb hcΦg)
  have hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((δA 1), 0)) ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])) := by
    rw [Rigidified.isEtaSection_one_iff]
    exact ⟨hη1, hrel0⟩
  have hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 (((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0)) ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) := by
    rw [Rigidified.isEtaSection_one_iff]
    exact ⟨hηW, hrel1⟩
  refine ⟨hc, hcb, hcΦg, L, hL, ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((δA 1), 0), ((t.XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : Ω))) hc).nMk ((verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), 0), hz₀, hz₁, (δA 1), (verschiebungInt (δA 0) - WittVector.teichmuller p ((Rigidified.awayHom (1 : Ω)) c) • (δA 1)), rfl, rfl, ?_, ?_⟩
  · intro j
    rw [map_sub, tangent_verschiebungInt, tangent_smul_witt, WittVector.teichmuller_coeff_zero, zero_sub,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  · by_contra hall
    push_neg at hall
    apply hδA.2.ne_zero
    exact Matrix.det_eq_zero_of_row_eq_zero 1 (fun j => by rw [Matrix.of_apply]; exact hall j)

end K86

namespace K85I

theorem isNoetherianRing_edgeRingCharP {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (EdgeFamily.edgeRingCharP p R) := by
  haveI : IsNoetherianRing (FormalOmega.edgeQuot R (0 : R)) :=
    show IsNoetherianRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {FormalOmega.edgeRel R (0:R)}) from inferInstance
  exact IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr R (0:R) p)) _ inferInstance

end K85I

set_option maxHeartbeats 4000000 in
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
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hyη : y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ≠ 0) :
    ∃ (hOD : FormalODModule.IsODHom (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).Φbar (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).Xbar ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).ρ)
      (hc : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsGradedS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (hcb : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsGradedSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω)))
      (L : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).M →+ ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hL : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).IsCanonicalLMap L)
      (z₀ z₁ : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).NMod)
      (hz₀ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsEtaSection ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 z₀
        ((p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p])))
      (hz₁ : ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsEtaSection ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hOD (Rigidified.awayHom (1 : Ω)) hc hcb hcΦg L hL 1 z₁
        ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]))
      (m₀ m₁ : ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).M),
      ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₀ = ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩ ∧
      ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).vRange.mkQ m₁ = ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jS ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩ ∧
      (∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j =
        -(Rigidified.awayHom (1 : Ω) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) * MvFormalGroup.CartierModule.tangent m₀ j) ∧
      ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0 := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have hpk : ((p : ℕ) : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hpE : ((p : ℕ) : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = 0 := by rw [← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))), hpk, map_zero]
  have hpΩ : ((p : ℕ) : Ω) = 0 := by rw [← map_natCast y, hpE, map_zero]
  haveI hcharΩ : CharP Ω p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ

  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI : IsNoetherianRing (WittVector p k ⧸ pIdeal p (WittVector p k)) := inferInstance
  haveI : IsNoetherianRing (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) := K85I.isNoetherianRing_edgeRingCharP
  have hadmE := CerednikDrinfeld.SpecialFormal.Rigidified.isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
    p k ι Φ X hXs hX4 f₀ m ρ₀ hρ₀ ρ₁.toSeries hρ₁h
  have hadm := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) y _ hadmE

  have hJ : y.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) = structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) :=
    RingHom.ext fun _ => rfl
  have hδ : (X.map y).IsHomogeneousVBasis (structureMap ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (fun i => baseChange y (γ i)) :=
    K82Edge.isHomogeneousVBasis_map_of_eq y hγ hJ
  have hδa : (X.map y).HasStructureConstants (fun i => baseChange y (γ i)) (EdgeFamily.edgeConstants p (y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) :=
    K82Edge.hasStructureConstants_map_edgeConstants y X γ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) hγa
  have ha : (X.map y).HasStructureConstants (fun i => baseChange y (γ i)) (EdgeFamily.edgeConstants p (0 : Ω) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))))) := by
    rw [← hyξ]
    exact hδa

  have hred : ∀ i : Fin 2, ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).redC (Rigidified.awayHom (1 : Ω)) ((fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i))) i) = (fun i => baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ i)))) i := by
    intro i
    refine MvFormalGroup.CartierModule.ext (funext fun j => ?_)
    simp only [Rigidified.redC, MvFormalGroup.CartierModule.baseChange,
      MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq]
    rw [MvPowerSeries.map_map, MvPowerSeries.map_map]
    rfl

  have hR := CerednikDrinfeld.FormalODModule.smul_rigidNum_map_single_eq_smul_baseChange_of_rigidNum_single_eq_of_edge_isogeny
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h
    Ω y (Rigidified.awayHom (1 : Ω)) hadm.2.2.1
  refine ⟨hadm.2.2.1, K86.etaSec1 p k ι Φ hcΦ rΦ Ω (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y) hadm.2.2.1 (fun i => baseChange y (γ i)) hδ (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ha a m rfl
    (fun i => baseChange (Rigidified.awayHom (1 : Ω)) (baseChange y (γ i))) (fun _ => rfl) (fun i => baseChange (reduceMap (Rigidified.awayHom (1 : Ω))) (baseChange (Ideal.Quotient.mk (pIdeal p Ω)) (baseChange y (γ i)))) hred ((reduceMap (Rigidified.awayHom (1 : Ω))) ((Ideal.Quotient.mk (pIdeal p Ω)) (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) rfl ?_ ?_⟩
  · intro hcb' hcΦg'
    exact (hR hcb' hcΦg' 0).trans (congrArg (fun w : CartierModule p (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).F => p ^ (a + m) • ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcb').nMk (w, 0))
      (K84Eta.bc3_single_zero X γ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) y (Ideal.Quotient.mk (pIdeal p Ω)) (reduceMap (Rigidified.awayHom (1 : Ω)))))
  · intro hcb' hcΦg'
    exact (hR hcb' hcΦg' 1).trans (congrArg (fun w : CartierModule p (((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).F => p ^ (a + m) • ((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcb').nVarpi (((((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).XbarS (Rigidified.awayHom (1 : Ω))).toGradedCartierModuleData (Rigidified.jSbar ι (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (Rigidified.awayHom (1 : Ω))) hcb').nMk (w, 0)))
      (K84Eta.bc3_single_one X γ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) y (Ideal.Quotient.mk (pIdeal p Ω)) (reduceMap (Rigidified.awayHom (1 : Ω))) hyξ))

end S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_ne_zero (solution)
