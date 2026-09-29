-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c16a0edc-3b80-548b-a98e-ea3233a6b695

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_MvFormalGroup_CartierModule_length_quotient_range_mapLinear_eq_of_finrank_eq_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace IsogColength

theorem length_quotient_range_eq_add {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (P₀ P₁ : Submodule R M') (hP : IsCompl P₀ P₁)
    (Q₀ Q₁ : Submodule R M) (hQ : IsCompl Q₀ Q₁) (f : M →ₗ[R] M')
    (h₀ : Submodule.map f Q₀ ≤ P₀) (h₁ : Submodule.map f Q₁ ≤ P₁) :
    Module.length R (M' ⧸ LinearMap.range f) =
      Module.length R (↥P₀ ⧸ Submodule.comap P₀.subtype (Submodule.map f Q₀)) +
        Module.length R (↥P₁ ⧸ Submodule.comap P₁.subtype (Submodule.map f Q₁)) := by
  classical
  set N₀ : Submodule R P₀ := Submodule.comap P₀.subtype (Submodule.map f Q₀) with hN₀
  set N₁ : Submodule R P₁ := Submodule.comap P₁.subtype (Submodule.map f Q₁) with hN₁
  let g : M' →ₗ[R] (↥P₀ ⧸ N₀) × (↥P₁ ⧸ N₁) :=
    LinearMap.prod (N₀.mkQ ∘ₗ Submodule.projectionOnto P₀ P₁ hP) (N₁.mkQ ∘ₗ Submodule.projectionOnto P₁ P₀ hP.symm)
  have hg_apply : ∀ x, g x = (N₀.mkQ (Submodule.projectionOnto P₀ P₁ hP x),
      N₁.mkQ (Submodule.projectionOnto P₁ P₀ hP.symm x)) := fun x => rfl

  have hsurj : Function.Surjective g := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N₀ a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N₁ b
    refine ⟨(x : M') + (y : M'), ?_⟩
    simp only [hg_apply, map_add, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right,
      add_zero, zero_add]

  have hker : LinearMap.ker g = LinearMap.range f := by
    ext m
    rw [LinearMap.mem_ker, hg_apply, Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨hm₀, hm₁⟩
      have hx : m = (Submodule.projectionOnto P₀ P₁ hP m : M') + (Submodule.projectionOnto P₁ P₀ hP.symm m : M') := by
        have := Submodule.projection_add_projection_eq_self hP m
        rw [Submodule.projection_apply, Submodule.projection_apply] at this
        exact this.symm
      rw [hx]
      have h0 : ((Submodule.projectionOnto P₀ P₁ hP m : ↥P₀) : M') ∈ LinearMap.range f :=
        LinearMap.map_le_range (Submodule.mem_comap.mp hm₀)
      have h1 : ((Submodule.projectionOnto P₁ P₀ hP.symm m : ↥P₁) : M') ∈ LinearMap.range f :=
        LinearMap.map_le_range (Submodule.mem_comap.mp hm₁)
      exact Submodule.add_mem _ h0 h1
    · rintro ⟨q, rfl⟩

      have hq : q ∈ Q₀ ⊔ Q₁ := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨q₀, hq₀, q₁, hq₁, rfl⟩ := Submodule.mem_sup.mp hq
      have hf₀ : f q₀ ∈ P₀ := h₀ (Submodule.mem_map_of_mem hq₀)
      have hf₁ : f q₁ ∈ P₁ := h₁ (Submodule.mem_map_of_mem hq₁)
      set a : ↥P₀ := ⟨f q₀, hf₀⟩ with ha
      set b : ↥P₁ := ⟨f q₁, hf₁⟩ with hb
      have hab : f (q₀ + q₁) = (a : M') + (b : M') := by rw [map_add]
      rw [hab, map_add, map_add, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right,
        Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, add_zero, zero_add]
      exact ⟨Submodule.mem_comap.mpr (Submodule.mem_map_of_mem hq₀),
        Submodule.mem_comap.mpr (Submodule.mem_map_of_mem hq₁)⟩
  have e : (M' ⧸ LinearMap.range f) ≃ₗ[R] (↥P₀ ⧸ N₀) × (↥P₁ ⧸ N₁) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)
  rw [e.length_eq, Module.length_prod]

theorem enat_eq_of_add_self_eq (c : ℕ∞) (h : ℕ) (hc : c + c = ((2 * h : ℕ) : ℕ∞)) : c = h := by
  induction c using ENat.recTopCoe with
  | top => exact absurd hc (by rw [top_add]; exact ENat.top_ne_coe _)
  | coe n =>
    have : n + n = 2 * h := by exact_mod_cast hc
    exact_mod_cast (show n = h by omega)

end IsogColength

open MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y Z : FormalODModule p K) (hY : Y.IsSpecial j) (hZ : Z.IsSpecial j)
    (hY4 : Y.HasHeight 4) (hZ4 : Z.HasHeight 4)
    (hcY : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (hcZ : IsCompl (Z.gradedPiece j 0) (Z.gradedPiece j 1))
    (ρ : SpecialFormal.Series K) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ (2 * h))
    (i : Fin 2) :
    Function.Injective (MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom) ∧
    Submodule.map (MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom) (Y.gradedSubmodule j (i : ℕ)) ≤
      Z.gradedSubmodule j (i : ℕ) ∧
    Module.length (WittVector p K)
        (↥(Z.gradedSubmodule j (i : ℕ)) ⧸
          Submodule.comap (Z.gradedSubmodule j (i : ℕ)).subtype
            (Submodule.map (MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom)
              (Y.gradedSubmodule j (i : ℕ)))) = h := by
  classical

  set φ : Y.F.Hom Z.F := hρ.1.1.toHom with hφdef
  have hφ : φ.toPowerSeries = ρ := rfl

  have hfin : Module.Finite K (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range φ.toPowerSeries)) := by
    rw [hφ]; exact hρ.2.1
  have hdeg : Module.finrank K (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range φ.toPowerSeries)) = p ^ (2 * h) := by
    have := hρ.2.2.2 K (RingHom.id K)
    rwa [Series.map_ringHom_id, ← hφ] at this

  have hinj : Function.Injective (mapLinear (p := p) φ) := by
    intro a b hab
    exact map_injective_of_finite_quotient p Y.F Z.F φ hfin (by simpa only [mapLinear_apply] using hab)

  have hdegree : ∀ (i : Fin 2) (x : CartierModule p Y.F), x ∈ Y.gradedSubmodule j (i : ℕ) →
      mapLinear (p := p) φ x ∈ Z.gradedSubmodule j (i : ℕ) := by
    intro i x hx
    rw [FormalODModule.mem_gradedSubmodule_iff] at hx ⊢
    rw [mapLinear_apply]
    exact CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece p j Y Z ρ hρ.1 (i : ℕ) x hx
  have hle : ∀ i : Fin 2, Submodule.map (mapLinear (p := p) φ) (Y.gradedSubmodule j (i : ℕ)) ≤
      Z.gradedSubmodule j (i : ℕ) := by
    intro i
    rintro _ ⟨x, hx, rfl⟩
    exact hdegree i x hx

  have htot := length_quotient_range_mapLinear_eq_of_finrank_eq_pow p Y.F Z.F φ (2 * h) hdeg

  have hcY' : IsCompl (Y.gradedSubmodule j 0) (Y.gradedSubmodule j 1) :=
    (FormalODModule.isCompl_gradedSubmodule_iff Y j 0 1).2 hcY
  have hcZ' : IsCompl (Z.gradedSubmodule j 0) (Z.gradedSubmodule j 1) :=
    (FormalODModule.isCompl_gradedSubmodule_iff Z j 0 1).2 hcZ
  have hsplit := IsogColength.length_quotient_range_eq_add (Z.gradedSubmodule j 0) (Z.gradedSubmodule j 1) hcZ'
    (Y.gradedSubmodule j 0) (Y.gradedSubmodule j 1) hcY' (mapLinear (p := p) φ) (hle 0) (hle 1)

  obtain ⟨γ, hγ⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_field p j Y hY
  obtain ⟨γ', hγ'⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_field p j Z hZ
  have hγD := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j Y γ hγ hcY).1
  have hγD' := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j Z γ' hγ' hcZ).1
  have hbal := CerednikDrinfeld.GradedCartierModuleData.length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung
    p (Y.toGradedCartierModuleData j hcY) (Z.toGradedCartierModuleData j hcZ) γ hγD γ' hγD'
    (mapLinear (p := p) φ) hinj (fun x => map_verschiebungInt φ x) (fun i x hx => hdegree i x hx)

  have hbal' : Module.length (WittVector p K) (↥(Z.gradedSubmodule j 0) ⧸
        Submodule.comap (Z.gradedSubmodule j 0).subtype
          (Submodule.map (mapLinear (p := p) φ) (Y.gradedSubmodule j 0))) =
      Module.length (WittVector p K) (↥(Z.gradedSubmodule j 1) ⧸
        Submodule.comap (Z.gradedSubmodule j 1).subtype
          (Submodule.map (mapLinear (p := p) φ) (Y.gradedSubmodule j 1))) := hbal
  rw [htot, hbal'] at hsplit
  have hc1 : Module.length (WittVector p K) (↥(Z.gradedSubmodule j 1) ⧸
        Submodule.comap (Z.gradedSubmodule j 1).subtype
          (Submodule.map (mapLinear (p := p) φ) (Y.gradedSubmodule j 1))) = h :=
    IsogColength.enat_eq_of_add_self_eq _ h hsplit.symm
  refine ⟨hinj, hle i, ?_⟩
  fin_cases i
  · show Module.length (WittVector p K) (↥(Z.gradedSubmodule j 0) ⧸
        Submodule.comap (Z.gradedSubmodule j 0).subtype
          (Submodule.map (mapLinear (p := p) φ) (Y.gradedSubmodule j 0))) = h
    exact hbal'.trans hc1
  · show Module.length (WittVector p K) (↥(Z.gradedSubmodule j 1) ⧸
        Submodule.comap (Z.gradedSubmodule j 1).subtype
          (Submodule.map (mapLinear (p := p) φ) (Y.gradedSubmodule j 1))) = h
    exact hc1

end S_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial (solution)
