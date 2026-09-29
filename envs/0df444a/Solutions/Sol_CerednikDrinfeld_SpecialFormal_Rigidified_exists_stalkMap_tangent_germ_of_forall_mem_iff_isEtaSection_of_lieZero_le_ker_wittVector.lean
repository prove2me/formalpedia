-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/808198d7-2eba-53fc-9dfc-4bbd3e63df1d

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_surjective_of_tangent_germ_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_inclBaseChange_eq_map_of_tangent_germ
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ
import Mathlib
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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

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
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie)) :
    ∃ (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
      (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ))),

      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) ∧

      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) ∧

      (∀ x w, u₁ x (FormalOmega.inclBaseChange (FormalOmega.locRing B x) (M' := ⟨N₀ x, hfull₀ x⟩) (M := ⟨N₁ x, hfull₁ x⟩) (hle x) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x w)) ∧
      (∀ x w, u₀ x (((FormalOmega.smulInto (p : ℤ_[p]) (hsmul x)).baseChange (FormalOmega.locRing B x) :
            FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
              FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x w)) ∧

      (∀ x, Function.Surjective (u₀ x)) ∧ (∀ x, Function.Surjective (u₁ x)) ∧

      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x →
          ∃ (f : B) (s : ↥(t.X.lieZero (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₀ y, u₀ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ y))) = LocalizedModule.mk s ⟨f, hy⟩) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x →
          ∃ (f : B) (s : ↥(t.X.lieOne (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₁ y, u₁ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ y))) = LocalizedModule.mk s ⟨f, hy⟩) ∧

      (∀ (x : PrimeSpectrum B) (v : ↥(N₀ x)),
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] v) ∈
            (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₁)).restrictScalars B ⊔
              x.asIdeal • (⊤ : Submodule B (FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))) →
          ∃ w ∈ N₁ x, (v : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w) ∧
      (∀ (x : PrimeSpectrum B) (v : ↥(N₁ x)),
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] v) ∈
            (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₀)).restrictScalars B ⊔
              x.asIdeal • (⊤ : Submodule B (FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))) →
          (v : Fin 2 → ℚ_[p]) ∈ N₀ x) := by
  have h0 : ∀ m ∈ Φ.lieZero (Rigidified.jbar ι), Φ.lieVarpi m = 0 := fun m hm => LinearMap.mem_ker.mp (h0Φ hm)
  obtain ⟨u₀, u₁, hg₀, hg₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ p ι Φ hΦ hΦ4 h0 hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁ hfull₀ hfull₁ hle hsmul Pi₀ Pi₁ hPi₀ hPi₁
  obtain ⟨hP₁, hP₂⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.stalkMap_inclBaseChange_eq_map_of_tangent_germ p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁ hfull₀ hfull₁ hle hsmul Pi₀ Pi₁ hPi₀ hPi₁ u₀ u₁ hg₀ hg₁
  obtain ⟨hO₀, hO₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.stalkMap_surjective_of_tangent_germ_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁ hfull₀ hfull₁ hle hsmul Pi₀ Pi₁ hPi₀ hPi₁ u₀ u₁ hg₀ hg₁
  obtain ⟨hC₀, hC₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁ hfull₀ hfull₁ hle hsmul Pi₀ Pi₁ hPi₀ hPi₁ u₀ u₁ hg₀ hg₁
  obtain ⟨hK₀, hK₁⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ N₁ hN₀ hN₁ hfull₀ hfull₁ hle hsmul Pi₀ Pi₁ hPi₀ hPi₁ u₀ u₁ hg₀ hg₁
  exact ⟨u₀, u₁, hg₀, hg₁, hP₁, hP₂, hO₀, hO₁, hC₀, hC₁, hK₀, hK₁⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector (solution)
