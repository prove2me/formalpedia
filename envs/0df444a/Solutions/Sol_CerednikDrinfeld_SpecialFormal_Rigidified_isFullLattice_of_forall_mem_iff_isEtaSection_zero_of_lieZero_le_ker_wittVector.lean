-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c9f9a43c-ff86-574d-9b3b-6ae17d6eb034

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace AFULL0_reduce

theorem isFullLattice_of_sandwich (p : ℕ) [Fact p.Prime] (N : Submodule ℤ_[p] (Fin 2 → ℚ_[p])) (a b : ℕ)
    (hlow : ∀ w : Fin 2 → ℤ_[p], ((p : ℚ_[p]) ^ a • fun j => ((w j : ℤ_[p]) : ℚ_[p])) ∈ N)
    (hup : ∀ v ∈ N, ∃ w : Fin 2 → ℤ_[p], (p : ℚ_[p]) ^ b • v = fun j => ((w j : ℤ_[p]) : ℚ_[p])) :
    LT.LatticeTree.IsFullLattice N := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpb : (p : ℚ_[p]) ^ b ≠ 0 := pow_ne_zero _ hp0

  let coeL : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℚ_[p]) :=
    LinearMap.pi fun j => (Algebra.linearMap ℤ_[p] ℚ_[p]).comp (LinearMap.proj j)
  let Z : Submodule ℤ_[p] (Fin 2 → ℚ_[p]) := LinearMap.range coeL
  have hZfg : Z.FG := by
    rw [show Z = (⊤ : Submodule ℤ_[p] (Fin 2 → ℤ_[p])).map coeL from (LinearMap.range_eq_map coeL)]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have hcoe_mem : ∀ w : Fin 2 → ℤ_[p], (fun j => ((w j : ℤ_[p]) : ℚ_[p])) ∈ Z :=
    fun w => LinearMap.mem_range.2 ⟨w, funext fun j => rfl⟩
  let φ : (Fin 2 → ℚ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℚ_[p]) := DistribSMul.toLinearMap ℤ_[p] _ (((p : ℚ_[p]) ^ b)⁻¹)
  have hφ : ∀ v, φ v = ((p : ℚ_[p]) ^ b)⁻¹ • v := fun v => rfl
  have hNle : N ≤ Z.map φ := by
    intro v hv
    obtain ⟨w, hw⟩ := hup v hv
    refine ⟨_, hcoe_mem w, ?_⟩
    rw [hφ, ← hw, inv_smul_smul₀ hpb]
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian ℤ_[p] ↥(Z.map φ) := isNoetherian_of_fg_of_noetherian _ (hZfg.map φ)
    have h1 : (Submodule.comap (Z.map φ).subtype N).FG := IsNoetherian.noetherian _
    have h2 := Submodule.FG.map (f := (Z.map φ).subtype) h1
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hNle] at h2
  · rw [eq_top_iff]
    rintro v -
    rw [← (Pi.basisFun ℚ_[p] (Fin 2)).sum_repr v]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have hmem : ((p : ℚ_[p]) ^ a • Pi.basisFun ℚ_[p] (Fin 2) j) ∈ N := by
      convert hlow (Pi.single j 1) using 2
      funext k
      simp only [Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp
    have := Submodule.smul_mem (Submodule.span ℚ_[p] (N : Set (Fin 2 → ℚ_[p]))) (((p : ℚ_[p]) ^ a)⁻¹)
      (Submodule.subset_span hmem)
    rwa [inv_smul_smul₀ (pow_ne_zero _ hp0)] at this

end AFULL0_reduce

open AFULL0_reduce in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) :
    ∀ x : PrimeSpectrum B, LT.LatticeTree.IsFullLattice (N₀ x) := by
  intro x
  obtain ⟨a, ha⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht x
  obtain ⟨b, hb⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht x
  exact isFullLattice_of_sandwich p (N₀ x) a b (fun w => (hN₀ x _).2 (ha w)) (fun v hv => hb v ((hN₀ x v).1 hv))

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector (solution)
