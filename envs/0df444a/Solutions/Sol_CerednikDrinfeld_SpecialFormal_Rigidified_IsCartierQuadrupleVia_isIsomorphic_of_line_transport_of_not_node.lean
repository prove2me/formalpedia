-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/decd87ab-1d20-531d-aba4-9c4c4cbdb6c5

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
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_apply_zero_eq_zero_and_ne_zero_of_not_and
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_exists_mem_etaPiece_tangent_eq_of_line_transport
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
import Theorems.Thm_CerednikDrinfeld_FormalODModule_not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber
import Theorems.Thm_CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_isIsomorphic_of_line_transport_of_not_node
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

noncomputable section

namespace ULbAsm

open MvFormalGroup MvFormalGroup.CartierModule

theorem exists_not_mem_span_pair {κ : Type} [Field κ] (u₁ u₂ : Fin 3 → κ) :
    ∃ δ : Fin 3 → κ, ∀ v s : κ, δ ≠ v • u₁ + s • u₂ := by
  classical
  have hlt : Module.finrank κ (Submodule.span κ ({u₁, u₂} : Set (Fin 3 → κ))) < Module.finrank κ (Fin 3 → κ) := by
    calc Module.finrank κ (Submodule.span κ ({u₁, u₂} : Set (Fin 3 → κ)))
        ≤ ({u₁, u₂} : Finset (Fin 3 → κ)).card := by
          rw [← Finset.coe_pair]; exact finrank_span_finset_le_card _
      _ ≤ 2 := Finset.card_le_two
      _ < 3 := by norm_num
      _ = Module.finrank κ (Fin 3 → κ) := by simp
  have hne : Submodule.span κ ({u₁, u₂} : Set (Fin 3 → κ)) ≠ ⊤ := by
    intro h; rw [h, finrank_top] at hlt; exact lt_irrefl _ hlt
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin 3 → κ, δ ∉ Submodule.span κ ({u₁, u₂} : Set (Fin 3 → κ)) := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr fun x _ => hall x)
  refine ⟨δ, fun v s h => hδ ?_⟩
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem charP_of_isNilpotent_dualNumber {p : ℕ} [hp : Fact p.Prime] {κ : Type} [Field κ]
    (hR : IsNilpotent ((p : ℕ) : DualNumber κ)) : CharP κ p := by
  obtain ⟨n, hn⟩ := hR
  have h : ((p : κ)) ^ n = 0 := by
    have := congrArg TrivSqZeroExt.fst hn
    simpa using this
  have hp0 : (p : κ) = 0 := pow_eq_zero_iff'.mp h |>.1
  exact (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0

theorem exists_smul_and_unique {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X X' : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F) (γ' : Fin 2 → CartierModule p X'.F)
    (hγ : X.IsHomogeneousVBasis j γ) (hγ' : X'.IsHomogeneousVBasis j γ')
    (Λ : X.Lie ≃ₗ[B] X'.Lie)
    (hΛ0 : Submodule.map Λ.toLinearMap (X.lieZero j) = X'.lieZero j)
    (hΛ1 : Submodule.map Λ.toLinearMap (X.lieOne j) = X'.lieOne j) (i : Fin 2) :
    (∃ lam : B, Λ (tangent (γ i)) = lam • tangent (γ' i)) ∧
    (∀ x₁ x₂ : B, x₁ • tangent (γ' i) = x₂ • tangent (γ' i) → x₁ = x₂) := by
  obtain ⟨⟨h0, h1⟩, -, -, -⟩ :=
    CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p j hB X γ hγ
  obtain ⟨⟨h0', h1'⟩, u0', u1', -⟩ :=
    CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p j hB X' γ' hγ'
  fin_cases i
  · have hmem : Λ (tangent (γ 0)) ∈ X'.lieZero j := by
      rw [← hΛ0]; exact Submodule.mem_map_of_mem h0
    obtain ⟨lam, hlam, -⟩ := u0' _ hmem
    refine ⟨⟨lam, hlam⟩, fun x₁ x₂ h => ?_⟩
    exact (u0' (x₁ • tangent (γ' 0)) (Submodule.smul_mem _ _ h0')).unique rfl h
  · have hmem : Λ (tangent (γ 1)) ∈ X'.lieOne j := by
      rw [← hΛ1]; exact Submodule.mem_map_of_mem h1
    obtain ⟨lam, hlam, -⟩ := u1' _ hmem
    refine ⟨⟨lam, hlam⟩, fun x₁ x₂ h => ?_⟩
    exact (u1' (x₁ • tangent (γ' 1)) (Submodule.smul_mem _ _ h1')).unique rfl h

theorem isNoetherianRing_dualNumber (κ : Type) [Field κ] : IsNoetherianRing (DualNumber κ) := inferInstance

theorem ringHom_eq_algebraMap_comp {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
    {κ : Type} [Field κ] [CharP κ p] (ψ : WittVector p k →+* DualNumber κ) :
    ψ = (algebraMap κ (DualNumber κ)).comp ((TrivSqZeroExt.fstHom κ κ κ).toRingHom.comp ψ) := by
  haveI : PerfectRing k p := inferInstance
  have key := CerednikDrinfeld.ringHom_comp_eq_of_fstHom_comp_eq p k κ ψ
    ((Algebra.ofId κ (DualNumber κ)).comp (TrivSqZeroExt.fstHom κ κ κ)) (by ext x <;> simp)
  exact key.symm

theorem hwin_of_forall_ne {p : ℕ} {κ : Type} [Field κ] (a : ℕ → Fin 2 → κ) (i₀ : Fin 2) (δ : Fin 3 → κ)
    (hδ : ∀ v s : κ, δ ≠ v • ![a 0 (FormalODModule.piIndex 0 i₀), -(a 0 (FormalODModule.piIndex 0 i₀) ^ p), -(a 1 i₀ ^ p)] +
        s • ![-(a 1 i₀), -(a 1 (FormalODModule.piIndex 0 i₀)), -(a 2 i₀)])
    (ν : ℕ → Fin 2 → κ)
    (hν : ν = fun m i => if m = 1 ∧ i = i₀ then δ 0 else
      if m = 1 ∧ i = FormalODModule.piIndex 0 i₀ then δ 1 else if m = 2 ∧ i = i₀ then δ 2 else 0) :
    ∀ c₁ c₂ : κ,
      ¬ (ν 1 i₀ = c₁ * a 0 (FormalODModule.piIndex 0 i₀) - c₂ * a 1 i₀ ∧
         ν 1 (FormalODModule.piIndex 0 i₀) =
           -(c₁ * a 0 (FormalODModule.piIndex 0 i₀) ^ p) - c₂ * a 1 (FormalODModule.piIndex 0 i₀) ∧
         ν 2 i₀ = -(c₁ * a 1 i₀ ^ p) - c₂ * a 2 i₀) := by
  have hpi : FormalODModule.piIndex 0 i₀ ≠ i₀ := by
    intro h
    have := congrArg Fin.val h
    simp [FormalODModule.piIndex] at this
    omega
  have hν1 : ν 1 i₀ = δ 0 := by simp [hν]
  have hν2 : ν 1 (FormalODModule.piIndex 0 i₀) = δ 1 := by simp [hν, hpi]
  have hν3 : ν 2 i₀ = δ 2 := by simp [hν]
  intro c₁ c₂ h
  obtain ⟨h1, h2, h3⟩ := h
  rw [hν1] at h1; rw [hν2] at h2; rw [hν3] at h3
  apply hδ c₁ c₂
  ext jj
  fin_cases jj
  · simp; linear_combination h1
  · simp; linear_combination h2
  · simp; linear_combination h3

theorem window_zero {κ : Type} [Field κ] (i₀ : Fin 2) (δ : Fin 3 → κ) (i : Fin 2) :
    (fun m i => if m = 1 ∧ i = i₀ then δ 0 else
      if m = 1 ∧ i = FormalODModule.piIndex 0 i₀ then δ 1 else if m = 2 ∧ i = i₀ then δ 2 else (0 : κ)) 0 i = 0 := by
  simp

theorem final_algebra {κ : Type} [Field κ] (A S c c' sx l y : κ) (hcc' : c' - c ≠ 0)
    (hsnd : A * sx = c * S) (hsnd' : A * (sx + l * y) = c' * S) :
    S = A * l / (c' - c) * y := by
  rw [div_mul_eq_mul_div, eq_div_iff hcc']
  linear_combination hsnd - hsnd'

theorem fst_snd_of_eq_mul {κ : Type} [Field κ] (lam x x' : DualNumber κ) (hlam1 : TrivSqZeroExt.fst lam = 1)
    (hxx : x' = lam * x) :
    TrivSqZeroExt.fst x' = TrivSqZeroExt.fst x ∧
      TrivSqZeroExt.snd x' = TrivSqZeroExt.snd x + TrivSqZeroExt.snd lam * TrivSqZeroExt.fst x := by
  subst hxx
  refine ⟨by rw [TrivSqZeroExt.fst_mul, hlam1, one_mul], by rw [DualNumber.snd_mul, hlam1, one_mul]⟩

end ULbAsm

open MvFormalGroup MvFormalGroup.CartierModule

namespace ULbBridge

section tangent
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

theorem tangent_teichmuller_smul_add_verschiebungInt (δ : R) (γ t : CartierModule p Φ) :
    tangent (WittVector.teichmuller p δ • γ + verschiebungInt t) = δ • tangent γ := by
  rw [map_add, tangent_smul_witt, tangent_verschiebungInt, add_zero, WittVector.teichmuller_coeff_zero]

theorem tangent_sum_teichmuller_smul_add_verschiebungInt {ι : Type} [Fintype ι] (δ : ι → R)
    (γ : ι → CartierModule p Φ) (t : CartierModule p Φ) :
    tangent ((∑ i, WittVector.teichmuller p (δ i) • γ i) + verschiebungInt t) = ∑ i, δ i • tangent (γ i) := by
  rw [map_add, tangent_verschiebungInt, add_zero, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tangent_smul_witt, WittVector.teichmuller_coeff_zero]

theorem tangent_teichmuller_smul_add_verschiebungInt₂ (δ₀ δ₁ : R) (γ₀ γ₁ t : CartierModule p Φ) :
    tangent (WittVector.teichmuller p δ₀ • γ₀ + verschiebungInt (WittVector.teichmuller p δ₁ • γ₁) +
      verschiebungInt (verschiebungInt t)) = δ₀ • tangent γ₀ := by
  rw [map_add, map_add, tangent_smul_witt, tangent_verschiebungInt, tangent_verschiebungInt, add_zero, add_zero,
    WittVector.teichmuller_coeff_zero]

end tangent

section sameY
variable {κ : Type} [Field κ] {n : ℕ}

theorem fst_eq_fst_of_smul_eq_apply_smul (A : Matrix (Fin n) (Fin n) κ)
    (Λ : (Fin n → DualNumber κ) → (Fin n → DualNumber κ))
    (hΛred : ∀ (w : Fin n → DualNumber κ) (i : Fin n), TrivSqZeroExt.fst (Λ w i) =
      (Matrix.mulVecLin A (fun j => TrivSqZeroExt.fst (w j))) i)
    (g g' : Fin n → DualNumber κ)
    (hg' : ∀ i, TrivSqZeroExt.fst (g' i) = (Matrix.mulVecLin A (fun j => TrivSqZeroExt.fst (g j))) i)
    (hne : ∃ i, TrivSqZeroExt.fst (g' i) ≠ 0)
    (x x' : DualNumber κ) (hΛx : Λ (x • g) = x • Λ g)
    (hline : ∀ i, x' * g' i = Λ (x • g) i) :
    TrivSqZeroExt.fst x' = TrivSqZeroExt.fst x := by
  obtain ⟨i, hi⟩ := hne
  have h1 : TrivSqZeroExt.fst x' * TrivSqZeroExt.fst (g' i) = TrivSqZeroExt.fst x * TrivSqZeroExt.fst (g' i) := by
    have := congrArg TrivSqZeroExt.fst (hline i)
    rw [TrivSqZeroExt.fst_mul, hΛx, Pi.smul_apply, smul_eq_mul, TrivSqZeroExt.fst_mul, hΛred, ← hg'] at this
    exact this
  exact mul_right_cancel₀ hi h1

theorem fst_eq_fst_of_smul_eq_apply_smul' (A : Matrix (Fin n) (Fin n) κ)
    (Λ : (Fin n → DualNumber κ) →ₗ[DualNumber κ] (Fin n → DualNumber κ))
    (hΛred : ∀ (w : Fin n → DualNumber κ) (i : Fin n), TrivSqZeroExt.fst (Λ w i) =
      (Matrix.mulVecLin A (fun j => TrivSqZeroExt.fst (w j))) i)
    (g g' : Fin n → DualNumber κ)
    (hg' : ∀ i, TrivSqZeroExt.fst (g' i) = (Matrix.mulVecLin A (fun j => TrivSqZeroExt.fst (g j))) i)
    (hne : ∃ i, TrivSqZeroExt.fst (g' i) ≠ 0)
    (x x' : DualNumber κ) (hline : x' • g' = Λ (x • g)) :
    TrivSqZeroExt.fst x' = TrivSqZeroExt.fst x :=
  fst_eq_fst_of_smul_eq_apply_smul A Λ hΛred g g' hg' hne x x' (Λ.map_smul x g)
    (fun i => by rw [← hline, Pi.smul_apply, smul_eq_mul])

end sameY

end ULbBridge

theorem ULbAsm.param_eq
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ]
    (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
    (t t' : Rigidified p Φ (DualNumber κ)) (ht : t.IsAdmissible ι ψR) (ht' : t'.IsAdmissible ι ψR)
    (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ))
    (σ₀ : Q.T₀ ≃ₗ[DualNumber κ] ↥(t.X.lieZero (structureMap ι ψR)))
    (σ₁ : Q.T₁ ≃ₗ[DualNumber κ] ↥(t.X.lieOne (structureMap ι ψR)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q σ₀ σ₁)
    (σ₀' : Q'.T₀ ≃ₗ[DualNumber κ] ↥(t'.X.lieZero (structureMap ι ψR)))
    (σ₁' : Q'.T₁ ≃ₗ[DualNumber κ] ↥(t'.X.lieOne (structureMap ι ψR)))
    (hQ' : t'.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q' σ₀' σ₁')
    (Λ : t.X.Lie ≃ₗ[DualNumber κ] t'.X.Lie)
    (ψκ : WittVector p k →+* κ) (hresψ : (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).comp ψR = ψκ)

    (hsmooth : ¬ ((∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieZero (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0) ∧
        (∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieOne (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0)))

    (u₀ v₀ : Series κ) (m : ℕ)
    (hu₀ : FormalODModule.IsODHom (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X u₀) (hv₀ : FormalODModule.IsODHom (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X v₀)
    (hvu : v₀.comp u₀ = Series.id κ) (huv : u₀.comp v₀ = Series.id κ)
    (hρ : ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp ((u₀.map (Ideal.Quotient.mk (pIdeal p κ))).comp (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)
      = ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)

    (hΛ0 : Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψR)) = t'.X.lieZero (structureMap ι ψR))
    (hΛ1 : Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψR)) = t'.X.lieOne (structureMap ι ψR))
    (hΛPi : ∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w))
    (hΛred : ∀ (w : t.X.Lie) (i : Fin 2), TrivSqZeroExt.fst (Λ w i) =
      (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun j => TrivSqZeroExt.fst (w j))) i)

    (hN : ∀ x, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x)
    (hline : ∀ (x : PrimeSpectrum (DualNumber κ)) (i : Fin 2) (v : Fin 2 → ℚ_[p])
        (f : DualNumber κ) (hf : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψR (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψR (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f))
        (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
        (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψR ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
        (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).M)
        (hm : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).vRange.mkQ m =
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩)
        (f' : DualNumber κ) (hf' : f' ∉ x.asIdeal) (hc' : t'.IsGradedS ι ψR (Rigidified.awayHom f'))
        (hcb' : t'.IsGradedSbar ι ψR (Rigidified.awayHom f')) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f'))
        (L' : _) (hL' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').IsCanonicalLMap L')
        (z' : _) (hz' : t'.IsEtaSection ι hcΦ rΦ ψR ht'.2.2.1 (Rigidified.awayHom f') hc' hcb' hcΦf' L' hL' i z' v)
        (m' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').M)
        (hm' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').vRange.mkQ m' =
          ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz'.1).1⟩),
        ∀ j : Fin 2, Rigidified.awayToLoc x f' hf' (MvFormalGroup.CartierModule.tangent m' j) =
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m l))
    (a ν : ℕ → Fin 2 → κ) (c c' : κ) (i₀ : Fin 2)
    (γt : Fin 2 → MvFormalGroup.CartierModule p t.X.F) (γt' : Fin 2 → MvFormalGroup.CartierModule p t'.X.F)
    (γb : Fin 2 → MvFormalGroup.CartierModule p (t.X.map (TrivSqZeroExt.fstHom κ κ κ).toRingHom).F)
    (hγtR : t.X.IsHomogeneousVBasis (structureMap ι ψR) γt)
    (hγtR' : t'.X.IsHomogeneousVBasis (structureMap ι ψR) γt')
    (hAt : t.X.HasStructureConstants γt (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hAt' : t'.X.HasStructureConstants γt' (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c' * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (ha0 : a 0 i₀ = 0) (hu : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (hX4 : (t.X.map (TrivSqZeroExt.fstHom κ κ κ).toRingHom).HasHeight 4)
    (hwin : ∀ c₁ c₂ : κ,
      ¬ (ν 1 i₀ = c₁ * a 0 (FormalODModule.piIndex 0 i₀) - c₂ * a 1 i₀ ∧
         ν 1 (FormalODModule.piIndex 0 i₀) =
           -(c₁ * a 0 (FormalODModule.piIndex 0 i₀) ^ p) - c₂ * a 1 (FormalODModule.piIndex 0 i₀) ∧
         ν 2 i₀ = -(c₁ * a 1 i₀ ^ p) - c₂ * a 2 i₀))
    (hred : ∀ i, MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom κ κ κ).toRingHom (γt i) = γb i)
    (hred' : ∀ i, MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom κ κ κ).toRingHom (γt' i) =
      MvFormalGroup.CartierModule.map hu₀.1.toHom (γb i))
    (hsep : IsHausdorff (Ideal.span {((p : ℕ) : DualNumber κ)}) (DualNumber κ)) :
    c = c' := by
  haveI hchar : CharP κ p := ULbAsm.charP_of_isNilpotent_dualNumber hR
  have hct := CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis p _ t.X γt hγtR
  have hct' := CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis p _ t'.X γt' hγtR'
  obtain ⟨L, hL⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (structureMap ι ψR) hsep t.X γt hγtR hct
  obtain ⟨L', hL'⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (structureMap ι ψR) hsep t'.X γt' hγtR' hct'

  have hfstτ : (fun l => TrivSqZeroExt.fst (MvFormalGroup.CartierModule.tangent (γt i₀) l)) = MvFormalGroup.CartierModule.tangent (γb i₀) := by
    rw [← hred i₀]; exact (MvFormalGroup.CartierModule.tangent_baseChangeEq (TrivSqZeroExt.fstHom κ κ κ).toRingHom rfl (γt i₀)).symm
  have hfstτ' : (fun l => TrivSqZeroExt.fst (MvFormalGroup.CartierModule.tangent (γt' i₀) l)) =
      (MvFormalGroup.linearPart u₀).mulVec (MvFormalGroup.CartierModule.tangent (γb i₀)) := by
    have h1 : (fun l => TrivSqZeroExt.fst (MvFormalGroup.CartierModule.tangent (γt' i₀) l)) =
        MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom κ κ κ).toRingHom (γt' i₀)) :=
      (MvFormalGroup.CartierModule.tangent_baseChangeEq (TrivSqZeroExt.fstHom κ κ κ).toRingHom rfl (γt' i₀)).symm
    rw [h1, hred' i₀]
    exact MvFormalGroup.CartierModule.tangent_map _ _
  have hg' : ∀ j, TrivSqZeroExt.fst (MvFormalGroup.CartierModule.tangent (γt' i₀) j) =
      (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun l => TrivSqZeroExt.fst (MvFormalGroup.CartierModule.tangent (γt i₀) l))) j := by
    intro j
    rw [Matrix.mulVecLin_apply, hfstτ]
    exact congrFun hfstτ' j
  have hne : ∃ j, TrivSqZeroExt.fst (MvFormalGroup.CartierModule.tangent (γt' i₀) j) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hb := (hγtR'.map (TrivSqZeroExt.fstHom κ κ κ).toRingHom).2
    have hrow : ∀ kk, (Matrix.of fun i kk => MvFormalGroup.CartierModule.tangent
        (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom κ κ κ).toRingHom (γt' i)) kk) i₀ kk = 0 := by
      intro kk
      rw [Matrix.of_apply]
      show MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.baseChangeEq (TrivSqZeroExt.fstHom κ κ κ).toRingHom rfl (γt' i₀)) kk = 0
      rw [MvFormalGroup.CartierModule.tangent_baseChangeEq]
      exact hall kk
    have hdet := Matrix.det_eq_zero_of_row_eq_zero i₀ hrow
    exact hb.ne_zero hdet

  obtain ⟨⟨lam, hlam⟩, huniq⟩ := ULbAsm.exists_smul_and_unique (structureMap ι ψR) hR t.X t'.X γt γt'
    hγtR hγtR' Λ hΛ0 hΛ1 i₀
  have hlam1 : TrivSqZeroExt.fst lam = 1 := by
    have h := ULbBridge.fst_eq_fst_of_smul_eq_apply_smul' (MvFormalGroup.linearPart u₀) Λ.toLinearMap hΛred
      (MvFormalGroup.CartierModule.tangent (γt i₀)) (MvFormalGroup.CartierModule.tangent (γt' i₀)) hg' hne 1 lam (by rw [one_smul]; exact hlam.symm)
    simpa using h

  have C2t := CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
    p κ (structureMap ι ψR) t.X γt hγtR hct a ν c hAt hν0 i₀ ha0 L hL
  have C2t' := CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
    p κ (structureMap ι ψR) t'.X γt' hγtR' hct' a ν c' hAt' hν0 i₀ ha0 L' hL'
  by_contra hneq
  have hcc' : c' - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hneq)
  apply CerednikDrinfeld.FormalODModule.not_exists_forall_period_variation_eq_mul_of_mem_etaPiece_of_hasStructureConstants_dualNumber
    p κ (structureMap ι ψR) t.X γt hγtR hct a ν c hAt hν0 i₀ ha0 hu hX4 hwin L hL
  refine ⟨a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.snd lam / (c' - c), ?_⟩
  intro z hz mm hm x hx
  obtain ⟨z', hz', mm', hm', htan⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.exists_mem_etaPiece_tangent_eq_of_line_transport
      p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ κ ψR hR t t' ht ht' Q Q' σ₀ σ₁ hQ σ₀' σ₁' hQ' Λ ψκ hresψ hsmooth
      u₀ v₀ m hu₀ hv₀ hvu huv hρ hΛ0 hΛ1 hΛPi hΛred hN hline hct hct' γt hγtR L hL L' hL' i₀ z hz mm hm
  obtain ⟨⟨x', hx'⟩, H'⟩ := C2t' z' hz' mm' hm'
  obtain ⟨hy, hsnd⟩ := (C2t z hz mm hm).2 x hx
  obtain ⟨hy', hsnd'⟩ := H' x' hx'
  have hxx : x' = lam * x := by
    apply huniq
    rw [← hx', htan, hx, LinearEquiv.map_smul, hlam, smul_smul, mul_comm]
  obtain ⟨hfx, hsx⟩ := ULbAsm.fst_snd_of_eq_mul lam x x' hlam1 hxx
  rw [hfx, hsx] at hsnd'
  exact ULbAsm.final_algebra _ _ c c' _ _ _ hcc' hsnd hsnd'

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra ℤ_[p] κ]
    (ψR : WittVector p k →+* DualNumber κ) (hR : IsNilpotent (p : DualNumber κ))
    (t t' : Rigidified p Φ (DualNumber κ)) (ht : t.IsAdmissible ι ψR) (ht' : t'.IsAdmissible ι ψR)
    (Q Q' : FormalOmega.DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) (DualNumber κ))
    (σ₀ : Q.T₀ ≃ₗ[DualNumber κ] ↥(t.X.lieZero (structureMap ι ψR)))
    (σ₁ : Q.T₁ ≃ₗ[DualNumber κ] ↥(t.X.lieOne (structureMap ι ψR)))
    (hQ : t.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q σ₀ σ₁)
    (σ₀' : Q'.T₀ ≃ₗ[DualNumber κ] ↥(t'.X.lieZero (structureMap ι ψR)))
    (σ₁' : Q'.T₁ ≃ₗ[DualNumber κ] ↥(t'.X.lieOne (structureMap ι ψR)))
    (hQ' : t'.IsCartierQuadrupleVia ι hcΦ rΦ ψR Q' σ₀' σ₁')
    (Λ : t.X.Lie ≃ₗ[DualNumber κ] t'.X.Lie)
    (ψκ : WittVector p k →+* κ) (hresψ : (((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).comp ψR = ψκ)

    (hsmooth : ¬ ((∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieZero (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0) ∧
        (∀ w ∈ (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieOne (structureMap ι ψκ), (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X.lieVarpi w = 0)))

    (u₀ v₀ : Series κ) (m : ℕ)
    (hu₀ : FormalODModule.IsODHom (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X u₀) (hv₀ : FormalODModule.IsODHom (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).X v₀)
    (hvu : v₀.comp u₀ = Series.id κ) (huv : u₀.comp v₀ = Series.id κ)
    (hρ : ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp ((u₀.map (Ideal.Quotient.mk (pIdeal p κ))).comp (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)
      = ((t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).Xbar.act ((p : Zp2 p) ^ (m + (t.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).n))).comp (t'.map ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ)).ρ)

    (hΛ0 : Submodule.map Λ.toLinearMap (t.X.lieZero (structureMap ι ψR)) = t'.X.lieZero (structureMap ι ψR))
    (hΛ1 : Submodule.map Λ.toLinearMap (t.X.lieOne (structureMap ι ψR)) = t'.X.lieOne (structureMap ι ψR))
    (hΛPi : ∀ w : t.X.Lie, Λ (t.X.lieVarpi w) = t'.X.lieVarpi (Λ w))
    (hΛred : ∀ (w : t.X.Lie) (i : Fin 2), TrivSqZeroExt.fst (Λ w i) =
      (Matrix.mulVecLin (MvFormalGroup.linearPart u₀) (fun j => TrivSqZeroExt.fst (w j))) i)

    (hN : ∀ x, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x)
    (hline : ∀ (x : PrimeSpectrum (DualNumber κ)) (i : Fin 2) (v : Fin 2 → ℚ_[p])
        (f : DualNumber κ) (hf : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψR (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψR (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f))
        (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
        (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψR ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
        (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).M)
        (hm : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).vRange.mkQ m =
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩)
        (f' : DualNumber κ) (hf' : f' ∉ x.asIdeal) (hc' : t'.IsGradedS ι ψR (Rigidified.awayHom f'))
        (hcb' : t'.IsGradedSbar ι ψR (Rigidified.awayHom f')) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψR (Rigidified.awayHom f'))
        (L' : _) (hL' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').IsCanonicalLMap L')
        (z' : _) (hz' : t'.IsEtaSection ι hcΦ rΦ ψR ht'.2.2.1 (Rigidified.awayHom f') hc' hcb' hcΦf' L' hL' i z' v)
        (m' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').M)
        (hm' : ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').vRange.mkQ m' =
          ((t'.XS (Rigidified.awayHom f')).toGradedCartierModuleData (Rigidified.jS ι ψR (Rigidified.awayHom f')) hc').u L' hL'.isCartierLMap.map_verschiebung ⟨z', (AddSubgroup.mem_inf.mp hz'.1).1⟩),
        ∀ j : Fin 2, Rigidified.awayToLoc x f' hf' (MvFormalGroup.CartierModule.tangent m' j) =
        ∑ l : Fin 2, Rigidified.locHom x (Λ (Pi.single l 1) j) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m l)) :
    t.IsIsomorphic t' := by

  haveI hchar : CharP κ p := ULbAsm.charP_of_isNilpotent_dualNumber hR
  have hπ : ((TrivSqZeroExt.fstHom κ κ κ).restrictScalars ℤ_[p] : DualNumber κ →+* κ) =
      (TrivSqZeroExt.fstHom κ κ κ).toRingHom := rfl
  set π : DualNumber κ →+* κ := (TrivSqZeroExt.fstHom κ κ κ).toRingHom with hπdef
  rw [hπ] at hresψ hsmooth hu₀ hv₀ hρ
  haveI : IsNoetherianRing (DualNumber κ) := ULbAsm.isNoetherianRing_dualNumber κ

  have htbar : (t.map π).IsAdmissible ι ψκ := by
    have h := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψR π t ht
    rwa [hresψ] at h
  have htbar' : (t'.map π).IsAdmissible ι ψκ := by
    have h := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψR π t' ht'
    rwa [hresψ] at h
  let X₀ : SpecialFormalODModule p (structureMap ι ψκ) := ⟨(t.map π).X, htbar.1, htbar.2.1⟩
  have hX₀ : X₀.toFormalODModule = t.X.map π := rfl
  have hsmooth₀ : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero (structureMap ι ψκ),
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne (structureMap ι ψκ),
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)) := hsmooth

  obtain ⟨γb, hγb⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_field p
    (structureMap ι ψκ) X₀.toFormalODModule X₀.isSpecial
  obtain ⟨a, ha, h01⟩ := CerednikDrinfeld.FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis p
    (structureMap ι ψκ) X₀.toFormalODModule γb hγb
  obtain ⟨i₀, ha0, hu⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_apply_zero_eq_zero_and_ne_zero_of_not_and X₀ hsmooth₀ γb hγb a ha h01

  obtain ⟨δ, hδ⟩ := ULbAsm.exists_not_mem_span_pair (κ := κ)
    ![a 0 (FormalODModule.piIndex 0 i₀), -(a 0 (FormalODModule.piIndex 0 i₀) ^ p), -(a 1 i₀ ^ p)]
    ![-(a 1 i₀), -(a 1 (FormalODModule.piIndex 0 i₀)), -(a 2 i₀)]
  set ν : ℕ → Fin 2 → κ := fun m i => if m = 1 ∧ i = i₀ then δ 0 else
      if m = 1 ∧ i = FormalODModule.piIndex 0 i₀ then δ 1 else if m = 2 ∧ i = i₀ then δ 2 else 0 with hνdef
  have hν0 : ∀ i, ν 0 i = 0 := fun i => by rw [hνdef]; exact ULbAsm.window_zero i₀ δ i
  have hν := CerednikDrinfeld.SpecialFormalODModule.forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
    X₀ γb hγb a ha h01 i₀ ha0 hu δ hδ

  have hψR : ψR = (algebraMap κ (DualNumber κ)).comp ψκ := by
    rw [← hresψ]
    exact ULbAsm.ringHom_eq_algebraMap_comp ψR
  have hj : structureMap ι ψR = (algebraMap κ (DualNumber κ)).comp (structureMap ι ψκ) := by
    show ψR.comp ι = ((algebraMap κ (DualNumber κ)).comp ψκ).comp ι
    rw [hψR]

  let wt : (t.X.map π).Hom X₀.toFormalODModule := FormalODModule.Hom.id _
  have hwt : wt.IsIso := ⟨FormalODModule.Hom.id _, FormalODModule.Hom.ext (Series.comp_id _),
    FormalODModule.Hom.ext (Series.comp_id _)⟩
  let w' : (t'.X.map π).Hom X₀.toFormalODModule := ⟨v₀, hv₀⟩
  have hw' : w'.IsIso := ⟨⟨u₀, hu₀⟩, FormalODModule.Hom.ext huv, FormalODModule.Hom.ext hvu⟩

  obtain ⟨c, γt, hγt, hAt, hlift⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
      X₀ hsmooth₀ γb hγb a ha h01 ν hν0 hν t.X wt hwt
  obtain ⟨c', γt', hγt', hAt', hlift'⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
      X₀ hsmooth₀ γb hγb a ha h01 ν hν0 hν t'.X w' hw'

  have hid : wt.toLawHom = MvFormalGroup.Hom.id _ := MvFormalGroup.Hom.ext rfl
  have hred : ∀ i, MvFormalGroup.CartierModule.baseChange π (γt i) = γb i := by
    intro i
    have h := hlift i
    rw [hid] at h
    exact (MvFormalGroup.CartierModule.map_id _).symm.trans h
  have hcomp : hu₀.1.toHom.comp w'.toLawHom = MvFormalGroup.Hom.id _ := MvFormalGroup.Hom.ext huv
  have hred' : ∀ i, MvFormalGroup.CartierModule.baseChange π (γt' i) =
      MvFormalGroup.CartierModule.map hu₀.1.toHom (γb i) := by
    intro i
    have h := congrArg (MvFormalGroup.CartierModule.map hu₀.1.toHom) (hlift' i)
    rw [← MvFormalGroup.CartierModule.map_comp, hcomp] at h
    exact (MvFormalGroup.CartierModule.map_id _).symm.trans h
  have hsep : IsHausdorff (Ideal.span {((p : ℕ) : DualNumber κ)}) (DualNumber κ) := by
    have hp : ((p : ℕ) : DualNumber κ) = 0 := by
      rw [← map_natCast (algebraMap κ (DualNumber κ)), CharP.cast_eq_zero, map_zero]
    rw [hp, Ideal.span_singleton_eq_bot.mpr rfl]
    exact ⟨fun x hx => by simpa [SModEq.bot] using hx 1⟩
  have hj' : ∀ (Y : FormalODModule p (DualNumber κ)) (γY : Fin 2 → MvFormalGroup.CartierModule p Y.F),
      Y.IsHomogeneousVBasis ((algebraMap κ (DualNumber κ)).comp (structureMap ι ψκ)) γY →
      Y.IsHomogeneousVBasis (structureMap ι ψR) γY := by
    intro Y γY h; rw [hj]; exact h
  have hγtR := hj' t.X γt hγt
  have hγtR' := hj' t'.X γt' hγt'

  have hcc : c = c' :=
    ULbAsm.param_eq p k ι Φ hΦ hΦ4 h0 hcΦ rΦ hrΦ κ ψR hR t t' ht ht' Q Q' σ₀ σ₁ hQ σ₀' σ₁' hQ' Λ ψκ hresψ hsmooth
      u₀ v₀ m hu₀ hv₀ hvu huv hρ hΛ0 hΛ1 hΛPi hΛred hN hline a ν c c' i₀ γt γt' γb hγtR hγtR' hAt hAt' hν0 ha0 hu
      htbar.2.1 (ULbAsm.hwin_of_forall_ne (p := p) a i₀ δ hδ ν hνdef) hred hred' hsep

  obtain ⟨u, hu, hmapu⟩ := CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants p
    (structureMap ι ψR) hsep t.X t'.X γt γt' hγtR hγtR' _ hAt (by rw [hcc]; exact hAt')

  have hured : u.toSeries.map π = u₀ := by
    have hnat : ∀ i, MvFormalGroup.CartierModule.map (u.map π).toLawHom
        (MvFormalGroup.CartierModule.baseChange π (γt i)) = MvFormalGroup.CartierModule.baseChange π (γt' i) := by
      intro i
      rw [← hmapu i]
      exact (MvFormalGroup.CartierModule.baseChangeEq_map π rfl rfl (φ := u.toLawHom)
        (ψ := (u.map π).toLawHom) (fun j => rfl) (γt i)).symm
    have key := CerednikDrinfeld.FormalODModule.hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis p
      (structureMap ι ψκ) X₀.toFormalODModule (t'.X.map π).F γb hγb (u.map π).toLawHom hu₀.1.toHom
      (fun i => by
        conv_lhs => rw [← hred i]
        exact (hnat i).trans (hred' i))
    exact congrArg MvFormalGroup.Hom.toPowerSeries key

  obtain ⟨uinv, huinv, hinvu⟩ := hu
  have hsurj : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hker : IsNilpotent (RingHom.ker π) := by
    have hmul : RingHom.ker π * RingHom.ker π = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      rw [RingHom.mem_ker] at ha hb
      rw [Ideal.mem_bot]
      change TrivSqZeroExt.fst a = 0 at ha
      change TrivSqZeroExt.fst b = 0 at hb
      ext
      · simp [ha]
      · simp [TrivSqZeroExt.snd_mul, ha, hb]
    refine ⟨2, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one]
    exact hmul
  refine CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
    ι π hsurj hker hR ψR t t' ht ht' u.toSeries uinv.toSeries u.isODHom uinv.isODHom
    (congrArg FormalODModule.Hom.toSeries huinv) (congrArg FormalODModule.Hom.toSeries hinvu) m ?_
  rw [hured]
  exact hρ

end
end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_isIsomorphic_of_line_transport_of_not_node
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadrupleVia_isIsomorphic_of_line_transport_of_not_node (solution)
