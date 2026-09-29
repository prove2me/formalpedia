-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f303b2ef-3ce4-598a-91a3-073c2d2be38e

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

namespace BCExist

variable {p : ℕ} [Fact p.Prime]

def relabel {T : Type} [CommRing T] {j : Zp2 p →+* T} (j' : Zp2 p →+* T)
    (E : GradedCartierModuleData p T j) : GradedCartierModuleData p T j' where
  M := E.M
  frobenius := E.frobenius
  verschiebung := E.verschiebung
  varpi := E.varpi
  piece := E.piece
  frobenius_smul := E.frobenius_smul
  smul_verschiebung := E.smul_verschiebung
  verschiebung_smul_frobenius := E.verschiebung_smul_frobenius
  frobenius_verschiebung := E.frobenius_verschiebung
  varpi_verschiebung := E.varpi_verschiebung
  varpi_frobenius := E.varpi_frobenius
  varpi_varpi := E.varpi_varpi
  isCompl_piece := E.isCompl_piece
  verschiebung_mem := E.verschiebung_mem
  frobenius_mem := E.frobenius_mem
  varpi_mem := E.varpi_mem

end BCExist

open BCExist

theorem solution
    (p : ℕ) [Fact p.Prime] {S T : Type} [CommRing S] [CommRing T]
    {jS : CerednikDrinfeld.Zp2 p →+* S} (jT : CerednikDrinfeld.Zp2 p →+* T) (ι : S →+* T)
    (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule) :
    ∃ DT : CerednikDrinfeld.GradedCartierModuleData p T jT,
      DT.IsSpecialCartierModule ∧
      ∃ g : DS.M →+ DT.M, CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' ι DS DT g := by
  classical

  obtain ⟨X, hc, γ, hγ, g, hbij, hW, hF, hV, hPi, hpc⟩ :=
    GradedCartierModuleData.exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
      p jS hS DS hDS

  have hγ' := hγ.map ι
  have hc' : IsCompl ((X.map ι).gradedPiece (ι.comp jS) 0) ((X.map ι).gradedPiece (ι.comp jS) 1) :=
    FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis p (ι.comp jS) (X.map ι) _ hγ'
  have hbc := FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p jS ι X γ hγ hc hc'
  obtain ⟨hγ'D, hspec'⟩ :=
    FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p (ι.comp jS) (X.map ι) _ hγ' hc'

  let e : (X.toGradedCartierModuleData jS hc).M ≃+ DS.M := AddEquiv.ofBijective g hbij
  have he : ∀ x, e x = g x := fun _ => rfl
  have heg : ∀ y, g (e.symm y) = y := fun y => by rw [← he, AddEquiv.apply_symm_apply]
  have hW' : ∀ (w : WittVector p S) (y : DS.M), e.symm (w • y) = w • e.symm y := fun w y => by
    apply e.injective; rw [AddEquiv.apply_symm_apply, he, hW, heg]
  have hF' : ∀ y, e.symm (DS.frobenius y) = (X.toGradedCartierModuleData jS hc).frobenius (e.symm y) := fun y => by
    apply e.injective; rw [AddEquiv.apply_symm_apply, he, hF, heg]
  have hV' : ∀ y, e.symm (DS.verschiebung y) = (X.toGradedCartierModuleData jS hc).verschiebung (e.symm y) := fun y => by
    apply e.injective; rw [AddEquiv.apply_symm_apply, he, hV, heg]
  have hPi' : ∀ y, e.symm (DS.varpi y) = (X.toGradedCartierModuleData jS hc).varpi (e.symm y) := fun y => by
    apply e.injective; rw [AddEquiv.apply_symm_apply, he, hPi, heg]

  have hpc' : ∀ (i : Fin 2) (y : DS.M), y ∈ DS.piece i → e.symm y ∈ (X.toGradedCartierModuleData jS hc).piece i := by
    intro i y hy
    have hmem : e.symm y ∈ (X.toGradedCartierModuleData jS hc).piece 0 ⊔ (X.toGradedCartierModuleData jS hc).piece 1 := by
      rw [(X.toGradedCartierModuleData jS hc).isCompl_piece.sup_eq_top]; trivial
    obtain ⟨x0, hx0, x1, hx1, hsum⟩ := Submodule.mem_sup.mp hmem
    have hy' : y = g x0 + g x1 := by rw [← map_add, hsum, heg]
    fin_cases i
    · have h1 : g x1 ∈ DS.piece 0 := by
        have : g x1 = y - g x0 := by rw [hy']; abel
        rw [this]; exact Submodule.sub_mem _ hy (hpc 0 x0 hx0)
      have h1' : g x1 ∈ DS.piece 1 := hpc 1 x1 hx1
      have hz : g x1 = 0 :=
        (Submodule.mem_bot _).mp (DS.isCompl_piece.disjoint.le_bot (Submodule.mem_inf.mpr ⟨h1, h1'⟩))
      have hx1z : x1 = 0 := hbij.1 (by rw [hz, map_zero])
      rw [← hsum, hx1z, add_zero]; exact hx0
    · have h0 : g x0 ∈ DS.piece 1 := by
        have : g x0 = y - g x1 := by rw [hy']; abel
        rw [this]; exact Submodule.sub_mem _ hy (hpc 1 x1 hx1)
      have h0' : g x0 ∈ DS.piece 0 := hpc 0 x0 hx0
      have hz : g x0 = 0 :=
        (Submodule.mem_bot _).mp (DS.isCompl_piece.disjoint.le_bot (Submodule.mem_inf.mpr ⟨h0', h0⟩))
      have hx0z : x0 = 0 := hbij.1 (by rw [hz, map_zero])
      rw [← hsum, hx0z, zero_add]; exact hx1

  obtain ⟨hγDX, -⟩ := FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p jS X γ hγ hc
  have hgγ : DS.IsHomogeneousVBasis (fun i => g (γ i)) := by
    refine ⟨fun i => hpc i _ (hγDX.1 i), fun y => ?_⟩
    obtain ⟨⟨c, z⟩, hz, huniq⟩ := hγDX.2 (e.symm y)
    refine ⟨(c, g z), ?_, ?_⟩
    · show y = (∑ i, WittVector.teichmuller p (c i) • g (γ i)) + DS.verschiebung (g z)
      have h1 := congrArg g hz
      rw [heg, map_add, map_sum, hV] at h1
      simp only [hW] at h1
      exact h1
    · rintro ⟨c', z'⟩ h'
      have key := huniq (c', e.symm z') (by
        apply hbij.1
        rw [heg, map_add, map_sum, hV, heg]
        simp only [hW]
        exact h')
      simp only [Prod.mk.injEq] at key
      refine Prod.ext key.1 ?_
      show z' = g z
      rw [← key.2, heg]

  refine ⟨relabel jT ((X.map ι).toGradedCartierModuleData (ι.comp jS) hc'), hspec',
    (MvFormalGroup.CartierModule.baseChange (Φ := X.F) ι).comp e.symm.toAddMonoidHom, ?_⟩
  refine ⟨fun w y => ?_, fun y => ?_, fun y => ?_, fun y => ?_, fun i y hy => ?_, ?_⟩
  · show MvFormalGroup.CartierModule.baseChange ι (e.symm (w • y)) = _
    rw [hW']; exact hbc.1 w _
  · show MvFormalGroup.CartierModule.baseChange ι (e.symm (DS.frobenius y)) = _
    rw [hF']; exact hbc.2.1 _
  · show MvFormalGroup.CartierModule.baseChange ι (e.symm (DS.verschiebung y)) = _
    rw [hV']; exact hbc.2.2.1 _
  · show MvFormalGroup.CartierModule.baseChange ι (e.symm (DS.varpi y)) = _
    rw [hPi']; exact hbc.2.2.2.1 _
  · show MvFormalGroup.CartierModule.baseChange ι (e.symm y) ∈ ((X.map ι).toGradedCartierModuleData (ι.comp jS) hc').piece i
    exact hbc.2.2.2.2.1 i _ (hpc' i y hy)
  · refine ⟨fun i => g (γ i), hgγ, ?_⟩
    show ((X.map ι).toGradedCartierModuleData (ι.comp jS) hc').IsHomogeneousVBasis (fun i => MvFormalGroup.CartierModule.baseChange ι (e.symm (g (γ i))))
    have : (fun i => MvFormalGroup.CartierModule.baseChange ι (e.symm (g (γ i)))) =
        (fun i => MvFormalGroup.CartierModule.baseChange (Φ := X.F) ι (γ i)) := by
      funext i; rw [← he, AddEquiv.symm_apply_apply]
    rw [this]; exact hγ'D

end S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree (solution)
