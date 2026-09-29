-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1b561341-566d-5344-9c9b-a8738ddc8ece

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_zero_of_lieZero_le_ker_lieVarpi
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_isNilpotent
import Theorems.Thm_PadicInt_addMonoidHom_map_smul_of_free
import Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
import Theorems.Thm_WittVector_ringHom_ext_padicInt
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

noncomputable section

namespace KbFrame

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

abbrev Kb : Type := WittVector p k ⧸ pIdeal p (WittVector p k)

abbrev Kb2 : Type := Kb p k ⧸ pIdeal p (Kb p k)

theorem isAlgClosed_of_ringEquiv {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

def ekKb : k ≃+* Kb p k :=
  Classical.choice (WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k)

theorem natCast_eq_zero_Kb : ((p : ℕ) : Kb p k) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))) p]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

theorem isNilpotent_Kb : IsNilpotent ((p : ℕ) : Kb p k) := by
  rw [natCast_eq_zero_Kb]; exact IsNilpotent.zero

theorem pIdeal_Kb_eq_bot : pIdeal p (Kb p k) = ⊥ := by
  show Ideal.span {((p : ℕ) : Kb p k)} = ⊥
  rw [natCast_eq_zero_Kb, Ideal.span_singleton_eq_bot]

def eKbKb2 : Kb p k ≃+* Kb2 p k :=
  ((Ideal.quotEquivOfEq (pIdeal_Kb_eq_bot p k)).trans (RingEquiv.quotientBot (Kb p k))).symm

theorem eKbKb2_apply (x : Kb p k) : eKbKb2 p k x = Ideal.Quotient.mk (pIdeal p (Kb p k)) x := rfl

def ekKb2 : k ≃+* Kb2 p k := (ekKb p k).trans (eKbKb2 p k)

theorem natCast_eq_zero_Kb2 : ((p : ℕ) : Kb2 p k) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (Kb p k))) p]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

theorem isNilpotent_Kb2 : IsNilpotent ((p : ℕ) : Kb2 p k) := by
  rw [natCast_eq_zero_Kb2]; exact IsNilpotent.zero

@[reducible] def fieldKb : Field (Kb p k) :=
  (MulEquiv.isField (Field.toIsField k) (ekKb p k).symm.toMulEquiv).toField

@[reducible] def fieldKb2 : Field (Kb2 p k) :=
  (MulEquiv.isField (Field.toIsField k) (ekKb2 p k).symm.toMulEquiv).toField

theorem charP_Kb : CharP (Kb p k) p :=
  charP_of_injective_ringHom (f := (ekKb p k).toRingHom) (fun a b h => (ekKb p k).injective h) p

theorem charP_Kb2 : CharP (Kb2 p k) p :=
  charP_of_injective_ringHom (f := (ekKb2 p k).toRingHom) (fun a b h => (ekKb2 p k).injective h) p

theorem isAlgClosed_Kb : @IsAlgClosed (Kb p k) (fieldKb p k) :=
  letI := fieldKb p k
  isAlgClosed_of_ringEquiv (ekKb p k)

theorem isAlgClosed_Kb2 : @IsAlgClosed (Kb2 p k) (fieldKb2 p k) :=
  letI := fieldKb2 p k
  isAlgClosed_of_ringEquiv (ekKb2 p k)

theorem perfectRing_Kb : PerfectRing (Kb p k) p := by
  letI := fieldKb p k
  haveI := isAlgClosed_Kb p k
  haveI := charP_Kb p k
  infer_instance

theorem perfectRing_Kb2 : PerfectRing (Kb2 p k) p := by
  letI := fieldKb2 p k
  haveI := isAlgClosed_Kb2 p k
  haveI := charP_Kb2 p k
  infer_instance

theorem isNoetherianRing_Kb : IsNoetherianRing (Kb p k) := by
  letI := fieldKb p k
  infer_instance

theorem isNoetherianRing_Kb2 : IsNoetherianRing (Kb2 p k) := by
  letI := fieldKb2 p k
  infer_instance

theorem isCompl_gradedPiece_Kb (j : Zp2 p →+* Kb p k) (X : FormalODModule p (Kb p k)) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) :=
  CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j (isNilpotent_Kb p k) X

theorem isCompl_gradedPiece_Kb2 (j : Zp2 p →+* Kb2 p k) (X : FormalODModule p (Kb2 p k)) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) :=
  CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j (isNilpotent_Kb2 p k) X

end KbFrame

namespace KbFrame

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local notation "𝕂" => (WittVector p k ⧸ pIdeal p (WittVector p k))
local notation "𝔼" => EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem comp_structureMap_eq (ι : Zp2 p →+* WittVector p k) (f₀ : 𝔼 →+* 𝕂)
    (hf₀ : f₀.comp (algebraMap 𝕂 𝔼) = RingHom.id 𝕂) :
    f₀.comp (structureMap ι ((algebraMap 𝕂 𝔼).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) =
      (Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι :=
  RingHom.ext fun x => by
    have := RingHom.congr_fun hf₀ (Ideal.Quotient.mk (pIdeal p (WittVector p k)) (ι x))
    simpa using this

theorem isSpecial_X0 (ι : Zp2 p →+* WittVector p k) (X : FormalODModule p 𝔼)
    (hXs : X.IsSpecial (structureMap ι ((algebraMap 𝕂 𝔼).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))))
    (f₀ : 𝔼 →+* 𝕂) (hf₀ : f₀.comp (algebraMap 𝕂 𝔼) = RingHom.id 𝕂) :
    (X.map f₀).IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := by
  have h := CerednikDrinfeld.FormalODModule.IsSpecial.map _ f₀ X hXs
  rwa [comp_structureMap_eq p k ι f₀ hf₀] at h

theorem isNoetherianRing_E : IsNoetherianRing 𝔼 := by
  letI := fieldKb p k
  haveI hNq : IsNoetherianRing (FormalOmega.edgeQuot 𝕂 (0 : 𝕂)) := by
    unfold FormalOmega.edgeQuot; infer_instance
  exact IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr 𝕂 (0 : 𝕂) p)) 𝔼 hNq

theorem hasHeight_X0 (X : FormalODModule p 𝔼) (hX4 : X.HasHeight 4) (f₀ : 𝔼 →+* 𝕂) :
    (X.map f₀).HasHeight 4 := by
  haveI := isNoetherianRing_E p k
  show FormalODModule.HasKernelOfDegree ((X.act (p : Zp2 p)).map f₀) (p ^ 4)
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f₀ _ (fun i => (X.isLawHom_act _).1 i) hX4

theorem hasHeight_map_Kb {B' : Type} [CommRing B'] (Y : FormalODModule p 𝕂) {h : ℕ} (hY : Y.HasHeight h)
    (f : 𝕂 →+* B') : (Y.map f).HasHeight h := by
  haveI := isNoetherianRing_Kb p k
  show FormalODModule.HasKernelOfDegree ((Y.act (p : Zp2 p)).map f) (p ^ h)
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f _ (fun i => (Y.isLawHom_act _).1 i) hY

theorem hasHeight_map_Kb2 {B' : Type} [CommRing B'] (Y : FormalODModule p (Kb2 p k)) {h : ℕ} (hY : Y.HasHeight h)
    (f : Kb2 p k →+* B') : (Y.map f).HasHeight h := by
  haveI := isNoetherianRing_Kb2 p k
  show FormalODModule.HasKernelOfDegree ((Y.act (p : Zp2 p)).map f) (p ^ h)
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f _ (fun i => (Y.isLawHom_act _).1 i) hY

theorem isIsogenyOfHeight_map_Kb {B' : Type} [CommRing B'] (Y Z : FormalODModule p 𝕂) (ρ : Series 𝕂) {h : ℕ}
    (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ h) (f : 𝕂 →+* B') :
    FormalODModule.IsIsogenyOfHeight (Y.map f) (Z.map f) (ρ.map f) h := by
  haveI := isNoetherianRing_Kb p k
  exact ⟨hρ.1.map f, CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f ρ hρ.1.constantCoeff hρ.2⟩

theorem isIsogenyOfHeight_map_Kb2 {B' : Type} [CommRing B'] (Y Z : FormalODModule p (Kb2 p k)) (ρ : Series (Kb2 p k)) {h : ℕ}
    (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ h) (f : Kb2 p k →+* B') :
    FormalODModule.IsIsogenyOfHeight (Y.map f) (Z.map f) (ρ.map f) h := by
  haveI := isNoetherianRing_Kb2 p k
  exact ⟨hρ.1.map f, CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f ρ hρ.1.constantCoeff hρ.2⟩

theorem residueMap_mk_eq :
    residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) = Ideal.Quotient.mk (pIdeal p 𝕂) := by
  apply Ideal.Quotient.ringHom_ext; ext x; simp [residueMap]

theorem reduceMap_id_eq : reduceMap (p := p) (RingHom.id 𝕂) = RingHom.id (Kb2 p k) := by
  apply Ideal.Quotient.ringHom_ext; ext x; simp [reduceMap, residueMap]

end KbFrame

end

noncomputable section

namespace N4rE

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem isAlgClosed_of_ringEquiv' {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local notation "𝕂" => (WittVector p k ⧸ pIdeal p (WittVector p k))
local notation "𝕂₂" => ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))
local notation "𝔼" => EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))
local notation "mkW" => Ideal.Quotient.mk (pIdeal p (WittVector p k))
local notation "mk₂" => Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))
local notation "g₂" => reduceMap (p := p) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))

def ekK2 : k ≃+* 𝕂₂ :=
  (Classical.choice (WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k)).trans
    (((Ideal.quotEquivOfEq (by
        show Ideal.span {((p : ℕ) : 𝕂)} = ⊥
        have : ((p : ℕ) : 𝕂) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))) p]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        rw [this, Ideal.span_singleton_eq_bot])).trans (RingEquiv.quotientBot 𝕂)).symm)

@[reducible] def fieldK2 : Field 𝕂₂ :=
  (MulEquiv.isField (Field.toIsField k) (ekK2 p k).symm.toMulEquiv).toField

theorem charP_K2 : CharP 𝕂₂ p :=
  charP_of_injective_ringHom (f := (ekK2 p k).toRingHom) (fun a b h => (ekK2 p k).injective h) p

theorem perfectRing_K2 : PerfectRing 𝕂₂ p := by
  letI := fieldK2 p k
  haveI : IsAlgClosed 𝕂₂ := isAlgClosed_of_ringEquiv' (ekK2 p k)
  haveI := charP_K2 p k
  infer_instance

theorem natCast_eq_zero_K2 : ((p : ℕ) : 𝕂₂) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (pIdeal p 𝕂)) p]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

theorem nodeBasis_generic (K : Type) [Field K] [CharP K p] [PerfectRing K p] (j : Zp2 p →+* K)
    (Y : FormalODModule p K) (δ : Fin 2 → CartierModule p Y.F)
    (hδ : Y.IsHomogeneousVBasis j δ) (ha : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : K) 0)) :
    (∀ i : Fin 2, endAct Y.varpiEnd (δ i) = verschiebungInt (δ i)) ∧
    (∀ r : Fin 2, (![δ 0, endAct Y.varpiEnd (δ 1)] r) ∈ Y.gradedPiece j 0) ∧
    (∀ m ∈ Y.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • (![δ 0, endAct Y.varpiEnd (δ 1)] r)) := by
  classical
  have hp0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨hPi0, hPi1⟩ :=
    CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
      p j (0 : K) 0 (zero_mul _) Y δ hδ ha
  rw [zero_pow hp0, sub_self, zero_smul, zero_add] at hPi0 hPi1
  have hPi : ∀ i : Fin 2, endAct Y.varpiEnd (δ i) = verschiebungInt (δ i) := by
    intro i; fin_cases i
    · exact hPi0
    · exact hPi1
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ :=
    CerednikDrinfeld.FormalODModule.exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
      p j (0 : K) 0 (zero_mul _) Y δ hδ ha
  have hnil : IsNilpotent ((p : ℕ) : K) := by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero
  have hcompl : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j hnil Y
  have hm0 : δ 0 ∈ Y.gradedPiece j 0 := hδ.1 0
  have hm1 : δ 1 ∈ Y.gradedPiece j 1 := hδ.1 1
  have hV1 : verschiebungInt (δ 1) ∈ Y.gradedPiece j 0 := by
    rw [← CerednikDrinfeld.FormalODModule.gradedPiece_add_two Y j 0]
    exact CerednikDrinfeld.FormalODModule.verschiebungInt_mem_gradedPiece_succ Y j 1 _ hm1
  have hV0 : verschiebungInt (δ 0) ∈ Y.gradedPiece j 1 :=
    CerednikDrinfeld.FormalODModule.verschiebungInt_mem_gradedPiece_succ Y j 0 _ hm0
  have he'0 : (![δ 0, endAct Y.varpiEnd (δ 1)] : Fin 2 → CartierModule p Y.F) 0 = b 0 := by
    simp [hb0]
  have he'1 : (![δ 0, endAct Y.varpiEnd (δ 1)] : Fin 2 → CartierModule p Y.F) 1 = b 3 := by
    simp [hPi 1, hb3]
  refine ⟨hPi, ?_, ?_⟩
  · intro r; fin_cases r
    · simpa using hm0
    · simpa [hPi 1] using hV1
  · intro m hm
    have hsum : m = b.repr m 0 • b 0 + b.repr m 1 • b 1 + b.repr m 2 • b 2 + b.repr m 3 • b 3 := by
      conv_lhs => rw [← b.sum_repr m]
      rw [Fin.sum_univ_four]
    have hM0 : b.repr m 0 • b 0 + b.repr m 3 • b 3 ∈ Y.gradedSubmodule j 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (by rw [hb0]; exact hm0))
        (Submodule.smul_mem _ _ (by rw [hb3]; exact hV1))
    have hM1 : b.repr m 1 • b 1 + b.repr m 2 • b 2 ∈ Y.gradedSubmodule j 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (by rw [hb1]; exact hm1))
        (Submodule.smul_mem _ _ (by rw [hb2]; exact hV0))
    have hM1' : b.repr m 1 • b 1 + b.repr m 2 • b 2 ∈ Y.gradedSubmodule j 0 := by
      have h1 : b.repr m 1 • b 1 + b.repr m 2 • b 2 = m - (b.repr m 0 • b 0 + b.repr m 3 • b 3) := by
        rw [eq_sub_iff_add_eq]
        refine Eq.trans ?_ hsum.symm
        ac_rfl
      rw [h1]
      exact Submodule.sub_mem _ ((Y.mem_gradedSubmodule_iff j 0 m).2 hm) hM0
    have hcompl' : IsCompl (Y.gradedSubmodule j 0) (Y.gradedSubmodule j 1) :=
      (CerednikDrinfeld.FormalODModule.isCompl_gradedSubmodule_iff Y j 0 1).2 hcompl
    have hzero : b.repr m 1 • b 1 + b.repr m 2 • b 2 = 0 :=
      (Submodule.disjoint_def.1 hcompl'.disjoint) _ hM1' hM1
    have hli := Fintype.linearIndependent_iff.1 b.linearIndependent
    have hc1 : b.repr m 1 = 0 ∧ b.repr m 2 = 0 := by
      have h := hli (![0, b.repr m 1, b.repr m 2, 0]) (by rw [Fin.sum_univ_four]; simpa using hzero)
      exact ⟨by simpa using h 1, by simpa using h 2⟩
    have hm' : m = b.repr m 0 • b 0 + b.repr m 3 • b 3 := by
      have h2 := hsum
      rw [hc1.1, hc1.2, zero_smul, zero_smul, add_zero, add_zero] at h2
      exact h2
    refine ⟨![b.repr m 0, b.repr m 3], ?_, ?_⟩
    · beta_reduce
      rw [Fin.sum_univ_two, he'0, he'1]
      simpa using hm'
    · intro w hw
      beta_reduce at hw
      rw [Fin.sum_univ_two, he'0, he'1] at hw
      have heq : w 0 • b 0 + w 1 • b 3 = b.repr m 0 • b 0 + b.repr m 3 • b 3 := hw.symm.trans hm'
      have hdiff : (w 0 - b.repr m 0) • b 0 + (w 1 - b.repr m 3) • b 3 = 0 := by
        rw [sub_smul, sub_smul, ← add_sub_add_comm, heq, sub_self]
      have h := hli (![w 0 - b.repr m 0, 0, 0, w 1 - b.repr m 3]) (by rw [Fin.sum_univ_four]; simpa using hdiff)
      funext r; fin_cases r
      · simpa [sub_eq_zero] using h 0
      · simpa [sub_eq_zero] using h 3

theorem nodeData (ι : Zp2 p →+* WittVector p k)
    (X : FormalODModule p 𝔼) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap 𝕂 𝔼).comp mkW)) γ)
    (hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p 𝕂))
    (f₀ : 𝔼 →+* 𝕂) (hf₀ : f₀.comp (algebraMap 𝕂 𝔼) = RingHom.id 𝕂)
    (hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p 𝕂) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p 𝕂) = 0) :
    (((X.map f₀).map mk₂).map g₂).IsHomogeneousVBasis (Rigidified.jSbar ι mkW (RingHom.id 𝕂))
        (fun i => baseChange g₂ (baseChange mk₂ (baseChange f₀ (γ i)))) ∧
    (((X.map f₀).map mk₂).map g₂).HasStructureConstants
        (fun i => baseChange g₂ (baseChange mk₂ (baseChange f₀ (γ i)))) (EdgeFamily.edgeConstants p (0 : 𝕂₂) 0) := by
  have hj : f₀.comp (structureMap ι ((algebraMap 𝕂 𝔼).comp mkW)) = (mkW).comp ι :=
    RingHom.ext fun x => by
      have := RingHom.congr_fun hf₀ (mkW (ι x))
      simpa using this
  have hγ1 : (X.map f₀).IsHomogeneousVBasis ((mkW).comp ι) (fun i => baseChange f₀ (γ i)) := by
    have := hγ.map f₀
    rwa [hj] at this
  have hconst : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (ξ η : R) (hξ : f ξ = 0) (hη : f η = 0),
      (fun m i => f (EdgeFamily.edgeConstants p ξ η m i)) = EdgeFamily.edgeConstants p (0 : S) 0 := by
    intro R S _ _ f ξ η hξ hη
    funext m i
    rw [EdgeFamily.edgeConstants_map, hξ, hη]
  have ha1 : (X.map f₀).HasStructureConstants (fun i => baseChange f₀ (γ i)) (EdgeFamily.edgeConstants p (0 : 𝕂) 0) := by
    have := hγa.map f₀
    rwa [hconst f₀ _ _ hf₀ξ hf₀η] at this
  have ha2 : ((X.map f₀).map mk₂).HasStructureConstants (fun i => baseChange mk₂ (baseChange f₀ (γ i)))
      (EdgeFamily.edgeConstants p (0 : 𝕂₂) 0) := by
    have := ha1.map mk₂
    rwa [hconst mk₂ _ _ (map_zero _) (map_zero _)] at this
  refine ⟨(hγ1.map mk₂).map g₂, ?_⟩
  have := ha2.map g₂
  rwa [hconst g₂ _ _ (map_zero _) (map_zero _)] at this

end N4rE

end

namespace B34N3

variable (p : ℕ) [Fact p.Prime]

theorem isField_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsField (WittVector p k ⧸ pIdeal p (WittVector p k)) := by
  obtain ⟨e⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  exact MulEquiv.isField (Field.toIsField k) e.symm.toMulEquiv

theorem pIdeal_eq_bot (K : Type) [Field K] [CharP K p] : pIdeal p K = ⊥ := by
  show Ideal.span {(p : K)} = ⊥
  rw [CharP.cast_eq_zero K p]
  exact Ideal.span_singleton_eq_bot.mpr rfl

noncomputable def quotEquiv (K : Type) [Field K] [CharP K p] : (K ⧸ pIdeal p K) ≃+* K :=
  (Ideal.quotEquivOfEq (pIdeal_eq_bot p K)).trans (RingEquiv.quotientBot K)

theorem isField_quot' (K : Type) [Field K] [CharP K p] : IsField (K ⧸ pIdeal p K) :=
  MulEquiv.isField (Field.toIsField K) (quotEquiv p K).toMulEquiv

theorem charP_quot_pIdeal {R : Type} [CommRing R] (h : IsField (R ⧸ pIdeal p R)) :
    CharP (R ⧸ pIdeal p R) p := by
  haveI : Nontrivial (R ⧸ pIdeal p R) := h.nontrivial
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton _))

section descent

variable {K : Type} [Field K] [CharP K p] [PerfectRing K p]

theorem node_varpi_eq (j : Zp2 p →+* K) (Y : FormalODModule p K)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδa : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : K) 0)) (i : Fin 2) :
    endAct Y.varpiEnd (δ i) = verschiebungInt (δ i) := by
  have h := CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
    p j (0 : K) 0 (zero_mul _) Y δ hδ hδa
  have h0 : WittVector.teichmuller p ((0 : K) ^ p) - WittVector.teichmuller p (0 : K) = 0 := by
    rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_self]
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [h.1, h0, zero_smul, zero_add]
  · rw [h.2, h0, zero_smul, zero_add]

theorem descent (j : Zp2 p →+* K) (Y : FormalODModule p K)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδa : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : K) 0))
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (c : ℤ_[p] →+* WittVector p K)
    (m : CartierModule p Y.F) (hm0 : m ∈ Y.gradedPiece j 0)
    (hmi : endAct Y.varpiEnd m = verschiebungInt m) :
    ∃ a : Fin 2 → ℤ_[p], m = c (a 0) • δ 0 + c (a 1) • verschiebungInt (δ 1) := by
  classical
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ :=
    CerednikDrinfeld.FormalODModule.exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
      p j (0 : K) 0 (zero_mul _) Y δ hδ hδa
  have hV := node_varpi_eq p j Y δ hδ hδa
  let P0 := Y.gradedSubmodule j 0
  let P1 := Y.gradedSubmodule j 1
  have hδ0 : δ 0 ∈ P0 := hδ.1 0
  have hδ1 : δ 1 ∈ P1 := hδ.1 1
  have hVδ0 : verschiebungInt (δ 0) ∈ P1 :=
    FormalODModule.verschiebungInt_mem_gradedPiece_succ Y j 0 _ hδ0
  have hVδ1 : verschiebungInt (δ 1) ∈ P0 := by
    have h2 := FormalODModule.verschiebungInt_mem_gradedPiece_succ Y j 1 _ hδ1
    rw [FormalODModule.gradedPiece_add_two] at h2
    exact h2
  set f := b.repr m with hf
  have hsum : m = f 0 • δ 0 + f 1 • δ 1 + f 2 • verschiebungInt (δ 0) + f 3 • verschiebungInt (δ 1) := by
    conv_lhs => rw [← b.sum_repr m]
    rw [Fin.sum_univ_four, hb0, hb1, hb2, hb3]

  have hv0 : f 1 • δ 1 + f 2 • verschiebungInt (δ 0) = 0 := by
    have h1 : f 1 • δ 1 + f 2 • verschiebungInt (δ 0) ∈ P1 :=
      P1.add_mem (P1.smul_mem _ hδ1) (P1.smul_mem _ hVδ0)
    have h0 : f 1 • δ 1 + f 2 • verschiebungInt (δ 0) ∈ P0 := by
      have e : f 1 • δ 1 + f 2 • verschiebungInt (δ 0) =
          m - (f 0 • δ 0 + f 3 • verschiebungInt (δ 1)) := by
        conv_rhs => rw [hsum]
        abel
      rw [e]
      exact P0.sub_mem hm0 (P0.add_mem (P0.smul_mem _ hδ0) (P0.smul_mem _ hVδ1))
    exact (AddSubgroup.disjoint_def.1 hc.disjoint) h0 h1
  have hf12 : f 1 = 0 ∧ f 2 = 0 := by
    have e := congrArg b.repr hv0
    rw [← hb1, ← hb2, map_add, map_smul, map_smul, b.repr_self, b.repr_self, map_zero] at e
    refine ⟨?_, ?_⟩
    · have e1 := congrArg (fun g => g 1) e
      simpa [Finsupp.single_apply] using e1
    · have e2 := congrArg (fun g => g 2) e
      simpa [Finsupp.single_apply] using e2
  have hm' : m = f 0 • δ 0 + f 3 • verschiebungInt (δ 1) := by
    rw [hsum, hf12.1, hf12.2, zero_smul, zero_smul, add_zero, add_zero]

  have hnil : IsNilpotent (p : K) := ⟨1, by rw [pow_one, CharP.cast_eq_zero]⟩
  have hinj := MvFormalGroup.CartierModule.verschiebungInt_injective_of_isNilpotent p hnil Y.F
  have e1 : endAct Y.varpiEnd m =
      verschiebungInt (WittVector.frobenius (f 0) • δ 0 +
        WittVector.frobenius (f 3) • verschiebungInt (δ 1)) := by
    rw [hm', map_add, endAct_smul_witt, endAct_smul_witt, hV 0, endAct_verschiebungInt, hV 1,
      smul_verschiebungInt, smul_verschiebungInt, ← map_add]
  have e2 : WittVector.frobenius (f 0) • δ 0 + WittVector.frobenius (f 3) • verschiebungInt (δ 1) =
      f 0 • δ 0 + f 3 • verschiebungInt (δ 1) := by
    apply hinj
    rw [← e1, hmi, hm']
  have hfix : WittVector.frobenius (f 0) = f 0 ∧ WittVector.frobenius (f 3) = f 3 := by
    have e := congrArg b.repr e2
    rw [← hb0, ← hb3, map_add, map_smul, map_smul, map_add, map_smul, map_smul,
      b.repr_self, b.repr_self] at e
    refine ⟨?_, ?_⟩
    · have e0 := congrArg (fun g => g 0) e
      simpa [Finsupp.single_apply] using e0
    · have e3 := congrArg (fun g => g 3) e
      simpa [Finsupp.single_apply] using e3
  obtain ⟨c', -, hc'fix⟩ :=
    WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p K
  have hcc : c' = c := WittVector.ringHom_ext_padicInt p K c' c
  subst hcc
  obtain ⟨a0, ha0⟩ := (hc'fix (f 0)).1 hfix.1
  obtain ⟨a1, ha1⟩ := (hc'fix (f 3)).1 hfix.2
  refine ⟨![a0, a1], ?_⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [ha0, ha1]
  exact hm'

theorem ringHom_padicInt_injective (c : ℤ_[p] →+* WittVector p K) : Function.Injective c := by
  obtain ⟨c', hinj, -⟩ :=
    WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p K
  rwa [WittVector.ringHom_ext_padicInt p K c' c] at hinj

theorem descent_unique (j : Zp2 p →+* K) (Y : FormalODModule p K)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδa : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : K) 0))
    (c : ℤ_[p] →+* WittVector p K) (a a' : Fin 2 → ℤ_[p])
    (h : c (a 0) • δ 0 + c (a 1) • verschiebungInt (δ 1) =
      c (a' 0) • δ 0 + c (a' 1) • verschiebungInt (δ 1)) : a = a' := by
  classical
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ :=
    CerednikDrinfeld.FormalODModule.exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
      p j (0 : K) 0 (zero_mul _) Y δ hδ hδa
  have hcinj := ringHom_padicInt_injective p c
  rw [← hb0, ← hb3] at h
  have e := congrArg b.repr h
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, b.repr_self, b.repr_self] at e
  funext i
  fin_cases i
  · have e0 := congrArg (fun g => g 0) e
    simp [Finsupp.single_apply] at e0
    exact hcinj e0
  · have e3 := congrArg (fun g => g 3) e
    simp [Finsupp.single_apply] at e3
    exact hcinj e3

end descent

section transport

variable {O B S : Type} [CommRing O] [CommRing B] [CommRing S]

theorem rigidNum_eq_nMk (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (ψ : O →+* B) (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (g : B →+* S) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (w : Fin 2 → ℤ_[p]) (mΦ : CartierModule p Φ.F)
    (hw : rΦ w = (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMk (mΦ, 0)) :
    Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w =
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk
        (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g mΦ), 0) := by
  rw [Rigidified.rigidNum, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hw,
    GradedCartierModuleData.nMap_nMk, GradedCartierModuleData.nMap_nMk, map_zero, map_zero]
  rfl

theorem transport (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (ψ : O →+* B) (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (g : B →+* S) (mΦ : CartierModule p Φ.F)
    (h0 : mΦ ∈ Φ.gradedPiece (Rigidified.jbar ι) 0)
    (hi : endAct Φ.varpiEnd mΦ = verschiebungInt mΦ) :
    Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g mΦ) ∈
        (t.XbarS g).gradedPiece (Rigidified.jPhiS ι ψ g) 0 ∧
      endAct (t.XbarS g).varpiEnd (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g mΦ)) =
        verschiebungInt (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g mΦ)) := by
  constructor
  · have h1 : Rigidified.bcPhi (Φ := Φ) ψ g mΦ ∈
        (Rigidified.PhibarS (Φ := Φ) ψ g).gradedPiece (Rigidified.jPhiS ι ψ g) 0 :=
      FormalODModule.baseChange_mem_gradedPiece (reduceMap g) _ _ 0
        (FormalODModule.baseChange_mem_gradedPiece (residueMap ψ) Φ (Rigidified.jbar ι) 0 h0)
    exact CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece p (Rigidified.jPhiS ι ψ g)
      (Rigidified.PhibarS (Φ := Φ) ψ g) (t.XbarS g) (t.ρ.map (reduceMap g)) (hOD.map (reduceMap g)) 0 _ h1
  · rw [← Rigidified.rhoC_endAct_varpiEnd ψ t hOD g, ← Rigidified.bcPhi_endAct_varpiEnd ψ g, hi,
      Rigidified.bcPhi_verschiebungInt, Rigidified.rhoC_verschiebungInt]

theorem jPhiS_eq_jSbar (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) :
    Rigidified.jPhiS ι ψ g = Rigidified.jSbar ι ψ g :=
  RingHom.ext fun _ => rfl

theorem nMk_smul_add_smul {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (u v : WittVector p B) (x y : D.M) :
    D.nMk (u • x + v • y, 0) = u • D.nMk (x, 0) + v • D.nMk (y, 0) := by
  rw [GradedCartierModuleData.smul_nMk, GradedCartierModuleData.smul_nMk, smul_zero, smul_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem nVarpi_nMk {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j) (x y : D.M) :
    D.nVarpi (D.nMk (x, y)) = D.nMk (D.varpi x, D.varpi y) := rfl

theorem main_general (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (ψ : O →+* B) (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (g : B →+* S) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (μ : (Fin 2 → ℤ_[p]) → CartierModule p Φ.F)
    (hμ0 : ∀ w, μ w ∈ Φ.gradedPiece (Rigidified.jbar ι) 0)
    (hμi : ∀ w, endAct Φ.varpiEnd (μ w) = verschiebungInt (μ w))
    (hμr : ∀ w, rΦ w = (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMk (μ w, 0))
    (hμadd : ∀ w w', μ (w + w') = μ w + μ w')
    (δ : Fin 2 → CartierModule p (t.XbarS g).F)
    (c : ℤ_[p] →+* WittVector p (S ⧸ pIdeal p S))
    (hnode : endAct (t.XbarS g).varpiEnd (δ 1) = verschiebungInt (δ 1))
    (hdesc : ∀ m : CartierModule p (t.XbarS g).F, m ∈ (t.XbarS g).gradedPiece (Rigidified.jSbar ι ψ g) 0 →
      endAct (t.XbarS g).varpiEnd m = verschiebungInt m →
      ∃ a : Fin 2 → ℤ_[p], m = c (a 0) • δ 0 + c (a 1) • verschiebungInt (δ 1))
    (huniq : ∀ a a' : Fin 2 → ℤ_[p], c (a 0) • δ 0 + c (a 1) • verschiebungInt (δ 1) =
      c (a' 0) • δ 0 + c (a' 1) • verschiebungInt (δ 1) → a = a') :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∀ w : Fin 2 → ℤ_[p],
      Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w =
        ∑ j : Fin 2, c (A.mulVec w j) •
          (![((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (δ 0, 0),
             ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nVarpi
               (((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nMk (δ 1, 0))] j) := by
  classical

  have hT : ∀ w, Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (μ w)) ∈
        (t.XbarS g).gradedPiece (Rigidified.jSbar ι ψ g) 0 ∧
      endAct (t.XbarS g).varpiEnd (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (μ w))) =
        verschiebungInt (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (μ w))) := by
    intro w
    have h := transport p ι ψ t hOD g (μ w) (hμ0 w) (hμi w)
    rwa [jPhiS_eq_jSbar] at h
  have H2 := fun w => hdesc _ (hT w).1 (hT w).2
  choose α hα using H2
  have α_add : ∀ w w', α (w + w') = α w + α w' := by
    intro w w'
    refine huniq _ _ ?_
    rw [← hα (w + w'), hμadd, map_add, map_add, hα w, hα w', Pi.add_apply, Pi.add_apply, map_add, map_add,
      add_smul, add_smul]
    abel
  have α_smul : ∀ (r : ℤ_[p]) (w : Fin 2 → ℤ_[p]), α (r • w) = r • α w :=
    fun r w => PadicInt.addMonoidHom_map_smul_of_free p (AddMonoidHom.mk' α α_add) r w
  let αl : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) :=
    { toFun := α, map_add' := α_add, map_smul' := α_smul }
  have hA : ∀ w, (LinearMap.toMatrix' αl).mulVec w = α w := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  refine ⟨LinearMap.toMatrix' αl, fun w => ?_⟩
  rw [hA w, rigidNum_eq_nMk p ι hcΦ rΦ ψ t hOD g hcb hcΦg w (μ w) (hμr w), hα w, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [nVarpi_nMk, map_zero, FormalODModule.toGradedCartierModuleData_varpi_apply, hnode]
  exact nMk_smul_add_smul p _ _ _ _ _

end transport

end B34N3

namespace B34N3

theorem phi_lift (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ μ : (Fin 2 → ℤ_[p]) → CartierModule p Φ.F,
      (∀ w, μ w ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) ∧
      (∀ w, endAct Φ.varpiEnd (μ w) = verschiebungInt (μ w)) ∧
      (∀ w, rΦ w = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (μ w, 0)) ∧
      (∀ w w', μ (w + w') = μ w + μ w') := by
  classical
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot_pIdeal p (isField_quot p k)
  obtain ⟨LΦ, hLΦ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ
  have hcrit : FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 := by
    have h := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi p
      ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ hΦ.1 h0Φ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
    simpa only [FormalODModule.map_id, RingHom.id_comp] using h
  have hiΦ : ∀ x ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
      ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd x := by
    intro x hx
    obtain ⟨g, hg⟩ := hcrit x hx
    exact ⟨g, by rw [verschiebungInt_apply_eq_verschiebung]; exact hg⟩
  have hLiΦ := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
      p k ι Φ hΦ hΦ4 hcΦ LΦ hLΦ 0 hiΦ x y hx hy
  have E4 := CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
    p k ι Φ hΦ hΦ4 hcΦ LΦ hLΦ 0 hiΦ hLiΦ
  have H1 : ∀ w : Fin 2 → ℤ_[p], ∃ x : CartierModule p Φ.F,
      x ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ) ∧
      endAct Φ.varpiEnd x = verschiebungInt x ∧
      rΦ w = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (x, 0) :=
    fun w => (E4.1 (rΦ w)).1 ((hrΦ LΦ hLΦ).mapsTo (Set.mem_univ w))
  choose μ hμ using H1
  refine ⟨μ, fun w => (hμ w).1, fun w => (hμ w).2.1, fun w => (hμ w).2.2, fun w w' => ?_⟩
  refine E4.2 _ _ (hμ _).1 (AddSubgroup.add_mem _ (hμ w).1 (hμ w').1) ?_
  have e : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (μ (w + w'), 0) =
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (μ w, 0) +
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (μ w', 0) := by
    rw [← (hμ (w + w')).2.2, map_add, (hμ w).2.2, (hμ w').2.2]
  rw [e, ← map_add, Prod.mk_add_mk, add_zero]
  try rfl

theorem node_side (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
    (hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
    (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) :
    endAct (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).varpiEnd (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))) = verschiebungInt (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))) ∧
    (∀ x : CartierModule p (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).F, x ∈ (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).gradedPiece (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) 0 →
      endAct (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).varpiEnd x = verschiebungInt x →
      ∃ a : Fin 2 → ℤ_[p], x = c (a 0) • (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))) + c (a 1) • verschiebungInt (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))))) ∧
    (∀ a a' : Fin 2 → ℤ_[p],
      c (a 0) • (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))) + c (a 1) • verschiebungInt (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))) =
        c (a' 0) • (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))) + c (a' 1) • verschiebungInt (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))) → a = a') := by
  classical

  have hf₀x : ∀ x, f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) x) = x := fun x => RingHom.congr_fun hf₀ x
  have hjX : (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp ((Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (f₀.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))))) = (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    refine RingHom.ext fun z => ?_
    simp only [Rigidified.jSbar, structureMap, RingHom.comp_apply, hf₀x]
  have hδ := ((hγ.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
  rw [hjX] at hδ
  have hδa := ((hγa.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
  have hconst : (fun n i => (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) ((Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (f₀ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k)) n i)))) =
      EdgeFamily.edgeConstants p (0 : ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) 0 := by
    funext n i
    rw [EdgeFamily.edgeRingConstants, EdgeFamily.edgeConstants_map, hf₀ξ, hf₀η, EdgeFamily.edgeConstants_map,
      map_zero, EdgeFamily.edgeConstants_map, map_zero]
  rw [hconst] at hδa

  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  letI fkb : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := (isField_quot p k).toField
  haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot_pIdeal p (isField_quot p k)
  obtain ⟨e1⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := IsAlgClosed.of_ringEquiv k _ e1
  have hFbb := isField_quot' p (WittVector p k ⧸ pIdeal p (WittVector p k))
  letI fkbb : Field ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) := hFbb.toField
  haveI : CharP ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := charP_quot_pIdeal p hFbb
  haveI : IsAlgClosed ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) := IsAlgClosed.of_ringEquiv _ _ (quotEquiv p (WittVector p k ⧸ pIdeal p (WittVector p k))).symm
  haveI : ExpChar ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := PerfectField.toPerfectRing p
  exact ⟨node_varpi_eq p _ _ _ hδ hδa 1,
    fun x hx hxi => descent p _ _ _ hδ hδa hcb c x hx hxi,
    fun a a' h => descent_unique p _ _ _ hδ hδa c a a' h⟩

end B34N3

namespace B34N3

theorem E_kbar (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ (et : Fin 2 → CartierModule p Φ.F) (P : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (c₁ : ℤ_[p] →+* WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))),
      IsUnit P.det ∧
      (∀ r, et r ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) ∧
      (∀ r, endAct Φ.varpiEnd (et r) = verschiebungInt (et r)) ∧
      (∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0, ∃! w : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)), m = ∑ r, w r • et r) ∧
      (∀ w, rΦ w = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (∑ r, c₁ ((P.mulVec w) r) • et r, 0)) := by
  classical

  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  letI fkb : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := (isField_quot p k).toField
  haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot_pIdeal p (isField_quot p k)
  obtain ⟨e1⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := IsAlgClosed.of_ringEquiv k _ e1

  obtain ⟨LΦ, hLΦ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ
  have hcrit : FormalODModule.CritChart.IsCritical Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 := by
    have h := CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_zero_of_lieZero_le_ker_lieVarpi p
      ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ hΦ.1 h0Φ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
    simpa only [FormalODModule.map_id, RingHom.id_comp] using h
  have hiΦ : ∀ x ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((0 : Fin 2) : ℕ),
      ∃ g : CartierModule p Φ.F, verschiebungInt g = endAct Φ.varpiEnd x := by
    intro x hx
    obtain ⟨g, hg⟩ := hcrit x hx
    exact ⟨g, by rw [verschiebungInt_apply_eq_verschiebung]; exact hg⟩
  have hLiΦ := fun x y hx hy =>
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
      p k ι Φ hΦ hΦ4 hcΦ LΦ hLΦ 0 hiΦ x y hx hy
  have E4 := CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk
    p k ι Φ hΦ hΦ4 hcΦ LΦ hLΦ 0 hiΦ hLiΦ

  obtain ⟨μ, hμ0, hμi, hμr, hμadd⟩ := phi_lift p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ

  obtain ⟨e, he_inv, he_uniq, he_fix, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ⟨Φ, hΦ, hΦ4⟩ 0 hcrit
  obtain ⟨c₁, hc₁inj, hc₁fix⟩ :=
    WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p (WittVector p k ⧸ pIdeal p (WittVector p k))
  have hcfix : ∀ x : ℤ_[p], WittVector.frobenius (c₁ x) = c₁ x := fun x => (hc₁fix (c₁ x)).2 ⟨x, rfl⟩

  have hcomb_inv : ∀ a : Fin 2 → ℤ_[p],
      (∑ r, c₁ (a r) • e r) ∈ FormalODModule.CritChart.invariants Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 :=
    fun a => (he_fix _).2 (fun r => hcfix (a r))
  have hcomb0 : ∀ a : Fin 2 → ℤ_[p], (∑ r, c₁ (a r) • e r) ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 :=
    fun a => (hcomb_inv a).1
  have huniq : ∀ a a' : Fin 2 → ℤ_[p],
      (∑ r, c₁ (a r) • e r) = ∑ r, c₁ (a' r) • e r → a = a' := by
    intro a a' h
    obtain ⟨ω, -, hω'⟩ := he_uniq _ (hcomb0 a)
    have h1 : (fun r => c₁ (a r)) = ω := hω' (fun r => c₁ (a r)) rfl
    have h2 : (fun r => c₁ (a' r)) = ω := hω' (fun r => c₁ (a' r)) h
    funext r
    exact hc₁inj (congrFun (h1.trans h2.symm) r)

  have Hq : ∀ w, ∃ a : Fin 2 → ℤ_[p], μ w = ∑ r, c₁ (a r) • e r := by
    intro w
    obtain ⟨ω, hω, -⟩ := he_uniq (μ w) (hμ0 w)
    have hinv : (∑ r, ω r • e r) ∈ FormalODModule.CritChart.invariants Φ ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0 := by
      rw [← hω]
      exact ⟨hμ0 w, by rw [hμi w, verschiebungInt_apply_eq_verschiebung]⟩
    have hfix := (he_fix ω).1 hinv
    choose a ha using fun r => (hc₁fix (ω r)).1 (hfix r)
    refine ⟨a, ?_⟩
    rw [hω]
    exact Finset.sum_congr rfl fun r _ => by rw [ha r]
  choose q hq using Hq
  have q_add : ∀ w w', q (w + w') = q w + q w' := by
    intro w w'
    apply huniq
    rw [← hq (w + w'), hμadd, hq w, hq w', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, map_add, add_smul]
  have q_smul : ∀ (s : ℤ_[p]) (w : Fin 2 → ℤ_[p]), q (s • w) = s • q w :=
    fun s w => PadicInt.addMonoidHom_map_smul_of_free p (AddMonoidHom.mk' q q_add) s w
  let qₗ : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) :=
    { toFun := q, map_add' := q_add, map_smul' := q_smul }
  have q_inj : Function.Injective q := by
    intro w w' h
    have h1 : μ w = μ w' := by rw [hq w, hq w', h]
    have h2 : rΦ w = rΦ w' := by rw [hμr w, hμr w', h1]
    exact (hrΦ LΦ hLΦ).injOn (Set.mem_univ _) (Set.mem_univ _) h2
  have q_surj : Function.Surjective q := by
    intro v
    have hvi : endAct Φ.varpiEnd (∑ r, c₁ (v r) • e r) = verschiebungInt (∑ r, c₁ (v r) • e r) := by
      rw [verschiebungInt_apply_eq_verschiebung]; exact (hcomb_inv v).2
    have hz : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (∑ r, c₁ (v r) • e r, 0) ∈
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 :=
      (E4.1 _).2 ⟨_, hcomb0 v, hvi, rfl⟩
    obtain ⟨w, -, hw⟩ := (hrΦ LΦ hLΦ).surjOn hz
    refine ⟨w, ?_⟩
    have hμw : μ w = ∑ r, c₁ (v r) • e r :=
      E4.2 _ _ (hμ0 w) (hcomb0 v) (by rw [← hμr w, hw]; rfl)
    apply huniq
    rw [← hq w, hμw]
  have hb : Function.Bijective qₗ := ⟨q_inj, q_surj⟩
  have hdet : IsUnit (LinearMap.toMatrix' qₗ).det := by
    rw [LinearMap.det_toMatrix']
    have heq : ((LinearEquiv.ofBijective qₗ hb : (Fin 2 → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) :
        (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])) = qₗ :=
      LinearMap.ext fun x => LinearEquiv.ofBijective_apply qₗ x
    rw [← heq]
    exact (LinearEquiv.ofBijective qₗ hb).isUnit_det'
  have hP : ∀ w, (LinearMap.toMatrix' qₗ).mulVec w = q w := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  refine ⟨e, LinearMap.toMatrix' qₗ, c₁, hdet, fun r => (he_inv r).1, fun r => ?_, he_uniq, fun w => ?_⟩
  · rw [verschiebungInt_apply_eq_verschiebung]; exact (he_inv r).2
  · rw [hμr w, hq w, hP w]
    rfl

section push

variable (p : ℕ) [Fact p.Prime] {O B S : Type} [CommRing O] [CommRing B] [CommRing S]

theorem bcPhi_smul {Φ : FormalODModule p (O ⧸ pIdeal p O)} (ψ : O →+* B) (g : B →+* S)
    (w : WittVector p (O ⧸ pIdeal p O)) (m : CartierModule p Φ.F) :
    Rigidified.bcPhi (Φ := Φ) ψ g (w • m) =
      WittVector.map (reduceMap g) (WittVector.map (residueMap ψ) w) • Rigidified.bcPhi (Φ := Φ) ψ g m := by
  show baseChange (reduceMap g) (baseChange (residueMap ψ) (w • m)) = _
  rw [baseChangeEq_smul_witt, baseChangeEq_smul_witt]
  rfl

theorem E_push (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (ψ : O →+* B) (g : B →+* S) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (et : Fin 2 → CartierModule p Φ.F) (P : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (c₁ : ℤ_[p] →+* WittVector p (O ⧸ pIdeal p O)) (c : ℤ_[p] →+* WittVector p (S ⧸ pIdeal p S))
    (hcc : ∀ x, WittVector.map (reduceMap g) (WittVector.map (residueMap ψ) (c₁ x)) = c x)
    (he0 : ∀ r, et r ∈ Φ.gradedPiece (Rigidified.jbar ι) 0)
    (hr : ∀ w, rΦ w = (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMk (∑ r, c₁ ((P.mulVec w) r) • et r, 0)) :
    (∀ r, Rigidified.bcPhi (Φ := Φ) ψ g (et r) ∈
        (Rigidified.PhibarS (Φ := Φ) ψ g).gradedPiece (Rigidified.jPhiS ι ψ g) 0) ∧
    ∀ w, (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap
        ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
        (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
        (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ w) =
      ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMk
        (∑ r, c ((P.mulVec w) r) • Rigidified.bcPhi (Φ := Φ) ψ g (et r), 0) := by
  refine ⟨fun r => ?_, fun w => ?_⟩
  · exact FormalODModule.baseChange_mem_gradedPiece (reduceMap g) _ _ 0
      (FormalODModule.baseChange_mem_gradedPiece (residueMap ψ) Φ (Rigidified.jbar ι) 0 (he0 r))
  · have hsum : Rigidified.bcPhi (Φ := Φ) ψ g (∑ r, c₁ ((P.mulVec w) r) • et r) =
        ∑ r, c ((P.mulVec w) r) • Rigidified.bcPhi (Φ := Φ) ψ g (et r) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [bcPhi_smul, hcc]
    rw [hr w, GradedCartierModuleData.nMap_nMk, map_zero]
    exact congrArg
      (fun x => ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMk (x, 0))
      hsum

end push

theorem E_push_N (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
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
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (et : Fin 2 → CartierModule p Φ.F) (P : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (c₁ : ℤ_[p] →+* WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (he0 : ∀ r, et r ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
    (hr : ∀ w, rΦ w = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (∑ r, c₁ ((P.mulVec w) r) • et r, 0)) :
    (∀ r, Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) (et r) ∈
        (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).gradedPiece
          (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) 0) ∧
    ∀ w, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap
        ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData
          (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg)
        (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
        (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
        (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (rΦ w) =
      ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData
          (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMk
        (∑ r, c ((P.mulVec w) r) • Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) (et r), 0) := by
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  have hF := isField_quot p k
  haveI : CharP ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := by
    letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := hF.toField
    haveI : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot_pIdeal p hF
    exact charP_quot_pIdeal p (isField_quot' p (WittVector p k ⧸ pIdeal p (WittVector p k)))
  have hcc : ((WittVector.map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp
      ((WittVector.map (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k))))).comp c₁)) = c :=
    WittVector.ringHom_ext_padicInt p _ _ _
  exact E_push p ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcΦg et P c₁ c
    (fun x => by rw [← hcc]; rfl) he0 hr

theorem E_seam (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
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
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) :
    ∃ (ee : Fin 2 → CartierModule p Φ.F) (P : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      IsUnit P.det ∧ (∀ r, ee r ∈ Φ.gradedPiece (Rigidified.jbar ι) 0) ∧
      (∀ m' ∈ Φ.gradedPiece (Rigidified.jbar ι) 0, ∃! w : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)), m' = ∑ r, w r • ee r) ∧
      ∀ w : Fin 2 → ℤ_[p], (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
          (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (rΦ w) =
        ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMk (∑ r, c ((P.mulVec w) r) • (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (ee r), 0) := by
  obtain ⟨et, P, c₁, hP, het0, -, het, hr⟩ := E_kbar p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
  obtain ⟨-, hpush⟩ := E_push_N p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ hcΦg c et P c₁ het0 hr
  exact ⟨et, P, hP, het0, het, hpush⟩

end B34N3

namespace N4rBridge

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

theorem nMk_eq_zero_iff {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j) (x : D.M × D.M) :
    D.nMk x = 0 ↔ ∃ t : D.M, D.verschiebung t = x.1 ∧ -D.varpi t = x.2 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m, hm⟩
    rw [nRelMap_apply, Prod.ext_iff] at hm
    exact ⟨D.ofSigma m, hm.1, by have h__af := hm.2; simp at h__af; exact h__af⟩
  · rintro ⟨t, ht, ht'⟩
    refine ⟨D.toSigma t, ?_⟩
    rw [nRelMap_apply, Prod.ext_iff]
    exact ⟨ht, by simp at ht' ⊢; exact ht'⟩

theorem eq_of_nMk_eq_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (hinj : ∀ m : D.M, D.varpi m = 0 → m = 0)
    (u v : D.M) (h : D.nMk (u, 0) = D.nMk (v, 0)) : u = v := by
  have h' : D.nMk ((u, 0) - (v, 0)) = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨t, ht, ht'⟩ := (nMk_eq_zero_iff _ _).mp h'
  rw [Prod.fst_sub] at ht
  rw [Prod.snd_sub, sub_zero, neg_eq_zero] at ht'
  have ht0 : t = 0 := hinj t ht'
  rw [ht0, map_zero] at ht
  exact sub_eq_zero.mp ht.symm

theorem eq_of_pow_smul_eq {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (hinj : ∀ m : D.M, D.varpi m = 0 → m = 0)
    (a : ℕ) (u v : D.M) (h : p ^ a • u = p ^ a • v) : u = v := by
  induction a with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    have h2 : (p : ℕ) • (p ^ n • u - p ^ n • v) = 0 := by
      rw [nsmul_sub, smul_smul, smul_smul, ← pow_succ', h, sub_self]
    have h3 : p ^ n • u - p ^ n • v = 0 := by
      apply hinj
      apply hinj
      rw [D.varpi_varpi, h2]
    exact sub_eq_zero.mp h3

theorem exists_det_eq (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (jY jZ : Zp2 p →+* K) (hj : jY = jZ)
    (Y Z : FormalODModule p K) (hY : Y.IsSpecial jY) (hZ : Z.IsSpecial jZ)
    (hY4 : Y.HasHeight 4) (hZ4 : Z.HasHeight 4)
    (hcY : IsCompl (Y.gradedPiece jY 0) (Y.gradedPiece jY 1))
    (hcZ : IsCompl (Z.gradedPiece jZ 0) (Z.gradedPiece jZ 1))
    (ρ : SpecialFormal.Series K) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ (2 * h))
    (c : ℤ_[p] →+* WittVector p K)
    (e : Fin 2 → CartierModule p Y.F)
    (he : ∀ m ∈ Y.gradedPiece jY 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r)
    (he0 : ∀ r, e r ∈ Y.gradedPiece jY 0)
    (P : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hP : IsUnit P.det)
    (e' : Fin 2 → CartierModule p Z.F)
    (he' : ∀ m ∈ Z.gradedPiece jZ 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e' r)
    (he'0 : ∀ r, e' r ∈ Z.gradedPiece jZ 0)
    (a : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ w : Fin 2 → ℤ_[p],
      p ^ a • (Z.toGradedCartierModuleData jZ hcZ).nMk (CartierModule.map hρ.1.1.toHom (∑ r, c ((P.mulVec w) r) • e r), 0) =
        p ^ a • ∑ s, c (A.mulVec w s) • (Z.toGradedCartierModuleData jZ hcZ).nMk (e' s, 0)) :
    ∃ u : ℤ_[p]ˣ, A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h := by
  classical
  subst hj
  have hinjZ : ∀ m : (Z.toGradedCartierModuleData jY hcZ).M, (Z.toGradedCartierModuleData jY hcZ).varpi m = 0 → m = 0 :=
    fun m hm => CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p jY Z hZ hZ4 m hm

  have hsum : ∀ w : Fin 2 → ℤ_[p], ∑ s, c (A.mulVec w s) • (Z.toGradedCartierModuleData jY hcZ).nMk (e' s, 0) = (Z.toGradedCartierModuleData jY hcZ).nMk (∑ s, c (A.mulVec w s) • e' s, 0) := by
    intro w
    have : ∀ s, c (A.mulVec w s) • (Z.toGradedCartierModuleData jY hcZ).nMk (e' s, 0) = (Z.toGradedCartierModuleData jY hcZ).nMk (c (A.mulVec w s) • e' s, 0) := fun s => by
      rw [smul_nMk, smul_zero]; try rfl
    simp_rw [this]
    rw [← map_sum]
    congr 1
    exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

  have hM : ∀ w : Fin 2 → ℤ_[p], CartierModule.map hρ.1.1.toHom (∑ r, c ((P.mulVec w) r) • e r) = ∑ s, c (A.mulVec w s) • e' s := by
    intro w
    have h1 := hA w
    rw [hsum, ← map_nsmul, ← map_nsmul, Prod.smul_mk, Prod.smul_mk, smul_zero] at h1
    exact eq_of_pow_smul_eq _ hinjZ a _ _ (eq_of_nMk_eq_nMk _ hinjZ _ _ h1)

  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hA' : ∀ r, CartierModule.mapLinear (p := p) hρ.1.1.toHom (e r) = ∑ s, c ((A * P⁻¹) s r) • e' s := by
    intro r
    have h1 := hM (P⁻¹.mulVec (Pi.single r 1))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec] at h1
    have hl : ∑ r', c ((Pi.single r (1 : ℤ_[p]) : Fin 2 → ℤ_[p]) r') • e r' = e r := by
      rw [Fintype.sum_eq_single r]
      · simp
      · intro b hb; simp [Pi.single_eq_of_ne hb]
    rw [hl] at h1
    rw [mapLinear_apply, h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mulVec_single_one]
    rfl

  obtain ⟨u, hu⟩ := CerednikDrinfeld.FormalODModule.exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
    p K jY Y Z hY hZ hY4 hZ4 hcY hcZ ρ h hρ c e he he0 e' he' he'0 (A * P⁻¹) hA'
  obtain ⟨v, hv⟩ := hP
  refine ⟨u * v, ?_⟩
  have hdet : (A * P⁻¹).det * P.det = A.det := by
    rw [← Matrix.det_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul P ⟨v, hv⟩, Matrix.mul_one]
  rw [← hdet, hu, ← hv, Units.val_mul]
  ring

end N4rBridge

namespace N4rPush

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

theorem basis_push {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφi : Function.Injective φ) (hφs : Function.Surjective φ)
    (j : Zp2 p →+* R) (X : FormalODModule p R)
    (hsurj : Function.Surjective (CartierModule.baseChange (p := p) (Φ := X.F) φ))
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hc' : IsCompl ((X.map φ).gradedPiece (φ.comp j) 0) ((X.map φ).gradedPiece (φ.comp j) 1))
    (e : Fin 2 → CartierModule p X.F) (he0 : ∀ r, e r ∈ X.gradedPiece j 0)
    (he : ∀ m ∈ X.gradedPiece j 0, ∃! w : Fin 2 → WittVector p R, m = ∑ r, w r • e r) :
    (∀ r, CartierModule.baseChange φ (e r) ∈ (X.map φ).gradedPiece (φ.comp j) 0) ∧
    ∀ m' ∈ (X.map φ).gradedPiece (φ.comp j) 0,
      ∃! w : Fin 2 → WittVector p S, m' = ∑ r, w r • CartierModule.baseChange φ (e r) := by
  classical
  have hinj : Function.Injective (CartierModule.baseChange (p := p) (Φ := X.F) φ) :=
    baseChangeEq_injective φ rfl hφi
  have hpush : ∀ (n : ℕ) (f : CartierModule p X.F), f ∈ X.gradedPiece j n →
      CartierModule.baseChange φ f ∈ (X.map φ).gradedPiece (φ.comp j) n :=
    fun n f hf => FormalODModule.baseChange_mem_gradedPiece φ X j n hf
  have hsum : ∀ w : Fin 2 → WittVector p R,
      CartierModule.baseChange φ (∑ r, w r • e r) = ∑ r, WittVector.map φ (w r) • CartierModule.baseChange φ (e r) := by
    intro w
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact baseChangeEq_smul_witt φ rfl (w r) (e r)
  refine ⟨fun r => hpush 0 _ (he0 r), ?_⟩
  intro m' hm'
  obtain ⟨m, rfl⟩ := hsurj m'
  have hm : m ∈ X.gradedPiece j 0 := by
    have htop : m ∈ X.gradedPiece j 0 ⊔ X.gradedPiece j 1 := by
      rw [hc.sup_eq_top]; exact AddSubgroup.mem_top m
    obtain ⟨m₀, hm₀, m₁, hm₁, hmm⟩ := AddSubgroup.mem_sup.mp htop
    have h1 : CartierModule.baseChange φ m₁ ∈ (X.map φ).gradedPiece (φ.comp j) 0 := by
      have : CartierModule.baseChange φ m₁ = CartierModule.baseChange φ m - CartierModule.baseChange φ m₀ := by
        rw [← map_sub, ← hmm, add_sub_cancel_left]
      rw [this]
      exact sub_mem hm' (hpush 0 _ hm₀)
    have h1' : CartierModule.baseChange φ m₁ ∈ (X.map φ).gradedPiece (φ.comp j) 0 ⊓ (X.map φ).gradedPiece (φ.comp j) 1 :=
      ⟨h1, hpush 1 _ hm₁⟩
    rw [hc'.inf_eq_bot] at h1'
    have h1'' : CartierModule.baseChange φ m₁ = 0 := AddSubgroup.mem_bot.mp h1'
    have : m₁ = 0 := hinj (by rw [h1'', map_zero])
    rw [← hmm, this, add_zero]; exact hm₀
  obtain ⟨w, hw, huniq⟩ := he m hm
  refine ⟨fun r => WittVector.map φ (w r), ?_, ?_⟩
  · show CartierModule.baseChange φ m = ∑ r, WittVector.map φ (w r) • CartierModule.baseChange φ (e r)
    rw [← hsum, ← hw]
  · intro w' hw'
    have hl : ∀ r, ∃ u, WittVector.map φ u = w' r := fun r => WittVector.map_surjective φ hφs (w' r)
    choose u hu using hl
    have hu' : (fun r => WittVector.map φ (u r)) = w' := funext hu
    have hm_eq : m = ∑ r, u r • e r := by
      apply hinj
      rw [hsum, hw']
      exact Finset.sum_congr rfl fun r _ => by rw [hu r]
    have := huniq u hm_eq
    subst this
    exact hu'.symm

end N4rPush

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

open KbFrame CerednikDrinfeld.GradedCartierModuleData

set_option maxHeartbeats 6400000 in
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
    (c : ℤ_[p] →+* WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (a : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ w : Fin 2 → ℤ_[p],
      p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) w =
        p ^ a • ∑ j : Fin 2, c (A.mulVec w j) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
                ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] j)) :
    ∃ u : ℤ_[p]ˣ, A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * m) := by
  classical
  letI instF : Field ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) := KbFrame.fieldKb2 p k
  haveI : CharP ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := KbFrame.charP_Kb2 p k
  haveI : PerfectRing ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := KbFrame.perfectRing_Kb2 p k

  have hXs0 : (X.map f₀).IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) := KbFrame.isSpecial_X0 p k ι X hXs f₀ hf₀
  have hX04 : (X.map f₀).HasHeight 4 := KbFrame.hasHeight_X0 p k X hX4 f₀
  have hZ : (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).IsSpecial (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) :=
    FormalODModule.IsSpecial.map _ (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) _ (FormalODModule.IsSpecial.map _ (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) _ hXs0)
  have hZ4 : (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).HasHeight 4 := KbFrame.hasHeight_map_Kb2 p k _ (KbFrame.hasHeight_map_Kb p k _ hX04 (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
  have hY : (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).IsSpecial (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) :=
    FormalODModule.IsSpecial.map _ (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) _ (FormalODModule.IsSpecial.map _ (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) _ hΦ)
  have hY4 : (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).HasHeight 4 := KbFrame.hasHeight_map_Kb2 p k _ (KbFrame.hasHeight_map_Kb p k _ hΦ4 (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
  have hρ1 : FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (4 * m) := by
    rw [KbFrame.residueMap_mk_eq]
    exact KbFrame.isIsogenyOfHeight_map_Kb p k _ _ _ hρ₀ (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))
  have hρbar : FormalODModule.IsIsogenyOfHeight (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) ((ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).map (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))) (2 * (2 * m)) := by
    rw [show 2 * (2 * m) = 4 * m by ring]
    exact KbFrame.isIsogenyOfHeight_map_Kb2 p k _ _ _ hρ1 (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
  have hj : (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) = (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    rfl

  obtain ⟨ee, P, hP, hee0, hee, hE⟩ := B34N3.E_seam p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ hcΦg c

  have hφ₁s : Function.Surjective (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) := by
    rw [KbFrame.residueMap_mk_eq]; exact Ideal.Quotient.mk_surjective
  have hφ₁i : Function.Injective (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) := by
    rw [KbFrame.residueMap_mk_eq, RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, KbFrame.pIdeal_Kb_eq_bot]
  have hφ₂s : Function.Surjective (reduceMap (p := p) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    rw [KbFrame.reduceMap_id_eq]; exact Function.surjective_id
  have hφ₂i : Function.Injective (reduceMap (p := p) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) := by
    rw [KbFrame.reduceMap_id_eq]; exact Function.injective_id
  have hsurj₁ : Function.Surjective (CartierModule.baseChange (p := p) (Φ := Φ.F) (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) := by
    letI : Algebra ℤ_[p] (WittVector p k ⧸ pIdeal p (WittVector p k)) := ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom)).toAlgebra
    exact MvFormalGroup.CartierModule.baseChange_surjective_of_surjective p _ hφ₁s Φ.F
  have hsurj₂ : Function.Surjective (CartierModule.baseChange (p := p) (Φ := (Φ.map (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k))))).F) (reduceMap (p := p) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))) := by
    letI : Algebra ℤ_[p] ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) := ((Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom))).toAlgebra
    exact MvFormalGroup.CartierModule.baseChange_surjective_of_surjective p _ hφ₂s (Φ.map (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k))))).F
  obtain ⟨he₁0, he₁⟩ := N4rPush.basis_push (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hφ₁i hφ₁s (Rigidified.jbar ι) Φ hsurj₁ hcΦ
    (KbFrame.isCompl_gradedPiece_Kb2 p k _ _) ee hee0 hee
  obtain ⟨he0, he⟩ := N4rPush.basis_push (reduceMap (p := p) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hφ₂i hφ₂s ((residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k)))).comp (Rigidified.jbar ι)) (Φ.map (residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hsurj₂
    (KbFrame.isCompl_gradedPiece_Kb2 p k _ _) hcΦg _ he₁0 he₁

  obtain ⟨e', he'def0, he'def1, he'0, he'⟩ : ∃ (e' : Fin 2 → CartierModule p (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).F),
      e' 0 = (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))) ∧ e' 1 = ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).varpi (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))) ∧
      (∀ r, e' r ∈ (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).gradedPiece (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) 0) ∧
      (∀ m' ∈ (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).gradedPiece (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) 0, ∃! w : Fin 2 → WittVector p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))), m' = ∑ r, w r • e' r) := by
    obtain ⟨hγb, hab⟩ := N4rE.nodeData p k ι X γ hγ hγa f₀ hf₀ hf₀ξ hf₀η
    obtain ⟨_, he'0x, he'x⟩ := N4rE.nodeBasis_generic p ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (fun i => (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ i))))) hγb hab
    exact ⟨![(baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), endAct (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).varpiEnd (baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))))], rfl, rfl, he'0x, he'x⟩

  have hrigid : ∀ w : Fin 2 → ℤ_[p],
      Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg w =
        ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (CartierModule.map hρbar.1.1.toHom (∑ r, c ((P.mulVec w) r) • (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (ee r)), 0) := by
    intro w
    show ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg).nMap ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb) (Rigidified.rhoC (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.rhoC_verschiebungInt (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀.1 (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.rhoC_endAct_varpiEnd (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcΦg) (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (rΦ w)) = _
    rw [hE w, nMap_nMk, map_zero]
    rfl
  have hb : ∀ j : Fin 2, (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0), ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] j) = ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (e' j, 0) := by
    have hnv : ∀ x : ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).M, ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (x, 0)) = ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).varpi x, 0) := fun x => by
      rw [nMk_apply, nMk_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
      unfold GradedCartierModuleData.nVarpi
      rw [Submodule.mapQ_apply]
      congr 1
      ext
      · rfl
      · show ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).toSigma (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).varpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).ofSigma 0)) = 0
        rw [map_zero, map_zero, map_zero]
    have hb0 : (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0), ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] 0) = ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (e' 0, 0) := by
      rw [he'def0]; rfl
    have hb1 : (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0), ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] 1) = ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (e' 1, 0) := by
      rw [he'def1]; exact hnv _
    intro j
    fin_cases j
    · exact hb0
    · exact hb1
  have hA' : ∀ w : Fin 2 → ℤ_[p],
      p ^ a • ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (CartierModule.map hρbar.1.1.toHom (∑ r, c ((P.mulVec w) r) • (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (ee r)), 0) =
        p ^ a • ∑ s, c (A.mulVec w s) • ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk (e' s, 0) := by
    intro w
    rw [← hrigid w, hA w]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by rw [hb s]
  exact N4rBridge.exists_det_eq ((WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) (Rigidified.jPhiS ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hj (Rigidified.PhibarS (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hY hZ hY4 hZ4 hcΦg hcb _ (2 * m) hρbar c (fun r => (Rigidified.bcPhi (Φ := Φ) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (ee r)) he he0 P hP e' he' he'0 a A hA'

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_of_rigidNum_eq_sum_smul_map_node (solution)
