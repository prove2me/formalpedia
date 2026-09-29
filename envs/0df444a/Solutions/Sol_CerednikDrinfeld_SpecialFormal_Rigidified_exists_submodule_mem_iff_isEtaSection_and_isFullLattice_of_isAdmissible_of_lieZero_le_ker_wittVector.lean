-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/452f0da2-06a5-5c11-bfc9-8eb01924f8b9

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_le_and_smul_mem_of_forall_mem_iff_isEtaSection
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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace QXA_reduce

theorem isFullLattice_of_le_of_smul_mem (p : ℕ) [Fact p.Prime]
    {N₀ N₁ : Submodule ℤ_[p] (Fin 2 → ℚ_[p])} (h₀ : LT.LatticeTree.IsFullLattice N₀)
    (hle : N₀ ≤ N₁) (hsmul : ∀ v ∈ N₁, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀) :
    LT.LatticeTree.IsFullLattice N₁ := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  let φ : (Fin 2 → ℚ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℚ_[p]) := DistribSMul.toLinearMap ℤ_[p] _ ((p : ℚ_[p])⁻¹)
  have hφ : ∀ v, φ v = (p : ℚ_[p])⁻¹ • v := fun v => rfl
  have hN₁le : N₁ ≤ N₀.map φ := by
    intro v hv
    refine ⟨algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v, hsmul v hv, ?_⟩
    rw [hφ, map_natCast, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian ℤ_[p] ↥(N₀.map φ) := isNoetherian_of_fg_of_noetherian _ (h₀.1.map φ)
    have h1 : (Submodule.comap (N₀.map φ).subtype N₁).FG := IsNoetherian.noetherian _
    have h2 := Submodule.FG.map (f := (N₀.map φ).subtype) h1
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN₁le] at h2
  · rw [eq_top_iff, ← h₀.2]
    exact Submodule.span_mono hle

end QXA_reduce

open QXA_reduce in
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∃ (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p])),
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) ∧
      (∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) ∧ (∀ x, LT.LatticeTree.IsFullLattice (N₁ x)) ∧
      (∀ x, N₀ x ≤ N₁ x) ∧
      (∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x) ∧
      (∀ v : Fin 2 → ℚ_[p], IsOpen {x : PrimeSpectrum B | v ∈ N₀ x}) ∧
      (∀ v : Fin 2 → ℚ_[p], IsOpen {x : PrimeSpectrum B | v ∈ N₁ x}) ∧

      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieOne (structureMap ι ψ) →
          ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieOne (structureMap ι ψ) →
              N₀ y = N₀ x) ∧
      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
          ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieZero (structureMap ι ψ) →
              N₁ y = N₁ x) ∧

      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieOne (structureMap ι ψ) →
          FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (N₀ x) 0) ∧
      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
          FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (N₁ x) (-1)) := by
  obtain ⟨N₀, N₁, hN₀, hN₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht
  obtain ⟨hle, hsmul⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.le_and_smul_mem_of_forall_mem_iff_isEtaSection p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁
  have hfull₀ := CerednikDrinfeld.SpecialFormal.Rigidified.isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ hN₀
  have hopen : ∀ (N : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p])) (i : Fin 2)
      (hN : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
      (v : Fin 2 → ℚ_[p]), IsOpen {x : PrimeSpectrum B | v ∈ N x} := by
    intro N i hN v
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN x v).1 hx
    refine ⟨(PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)), ?_, (PrimeSpectrum.basicOpen f).isOpen,
      (PrimeSpectrum.mem_basicOpen _ _).2 hf⟩
    intro y hy
    exact (hN y v).2 ⟨f, (PrimeSpectrum.mem_basicOpen _ _).1 hy, hc, hcb, hcΦf, L, hL, z, hz⟩
  exact ⟨N₀, N₁, hN₀, hN₁, hfull₀, fun x => isFullLattice_of_le_of_smul_mem p (hfull₀ x) (hle x) (hsmul x),
    hle, hsmul, hopen N₀ 0 hN₀, hopen N₁ 1 hN₁,
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ hN₀,
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₁ hN₁,
    CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ hN₀,
    CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₁ hN₁⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector (solution)
