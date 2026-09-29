-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/395a0577-655f-535c-b02b-5a2c27aa6e62

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace B4bpAsm

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ}

theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

noncomputable def geomPt {S : Type} [CommRing S] (𝔭 : PrimeSpectrum S) :
    S →+* AlgebraicClosure (FractionRing (S ⧸ 𝔭.asIdeal)) :=
  (algebraMap (FractionRing (S ⧸ 𝔭.asIdeal)) (AlgebraicClosure (FractionRing (S ⧸ 𝔭.asIdeal)))).comp
    ((algebraMap (S ⧸ 𝔭.asIdeal) (FractionRing (S ⧸ 𝔭.asIdeal))).comp (Ideal.Quotient.mk 𝔭.asIdeal))

theorem geomPt_eq_zero_iff {S : Type} [CommRing S] (𝔭 : PrimeSpectrum S) (s : S) :
    geomPt 𝔭 s = 0 ↔ s ∈ 𝔭.asIdeal := by
  unfold geomPt
  rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap (FractionRing (S ⧸ 𝔭.asIdeal)) _).injective,
    map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ 𝔭.asIdeal) (FractionRing (S ⧸ 𝔭.asIdeal))),
    Ideal.Quotient.eq_zero_iff_mem]

theorem eq_zero_of_forall_geomPt_eq_zero {S : Type} [CommRing S] [IsReduced S] (s : S)
    (h : ∀ 𝔭 : PrimeSpectrum S, geomPt 𝔭 s = 0) : s = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  exact (geomPt_eq_zero_iff ⟨J, hJ⟩ s).mp (h ⟨J, hJ⟩)

end B4bpAsm

open B4bpAsm CerednikDrinfeld.GradedCartierModuleData

theorem solution
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (hp0 : ((p : ℕ) : S) = 0)
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (ζ : (X.toGradedCartierModuleData j hc).NMod)
    (hζ : ζ ∈ (X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung)
    (hp : p • ζ = 0) :
    ζ = 0 := by
  classical

  let K : PrimeSpectrum S → Type := fun 𝔭 => AlgebraicClosure (FractionRing (S ⧸ 𝔭.asIdeal))
  let φ : ∀ 𝔭 : PrimeSpectrum S, S →+* K 𝔭 := fun 𝔭 => geomPt 𝔭
  have hpK : ∀ 𝔭, ((p : ℕ) : K 𝔭) = 0 := fun 𝔭 => by rw [← map_natCast (φ 𝔭) p, hp0, map_zero]
  haveI hchar : ∀ 𝔭, CharP (K 𝔭) p := fun 𝔭 => (CharP.charP_iff_prime_eq_zero Fact.out).mpr (hpK 𝔭)
  have hpKnil : ∀ 𝔭, IsNilpotent ((p : ℕ) : K 𝔭) := fun 𝔭 => ⟨1, by rw [pow_one, hpK]⟩
  have hpSnil : IsNilpotent ((p : ℕ) : S) := ⟨1, by rw [pow_one, hp0]⟩

  have hcK : ∀ 𝔭, IsCompl (((X.map (φ 𝔭)).gradedPiece ((φ 𝔭).comp j)) 0) (((X.map (φ 𝔭)).gradedPiece ((φ 𝔭).comp j)) 1) :=
    fun 𝔭 => CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hpKnil 𝔭) _
  have hγK : ∀ 𝔭, (X.map (φ 𝔭)).IsHomogeneousVBasis ((φ 𝔭).comp j)
      (fun i => CartierModule.baseChange (Φ := X.F) (φ 𝔭) (γ i)) := fun 𝔭 => hγ.map (φ 𝔭)
  have hD : (X.toGradedCartierModuleData j hc).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j X γ hγ hc).2
  have hDK : ∀ 𝔭, ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).IsSpecialCartierModule :=
    fun 𝔭 => (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ (hγK 𝔭) (hcK 𝔭)).2
  have hLK : ∀ 𝔭, ∃ L' : ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).M →+
      ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).NMod,
      ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).IsCanonicalLMap L' :=
    fun 𝔭 => CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
      ((φ 𝔭).comp j) (isHausdorff_of_isNilpotent (hpKnil 𝔭)) _ _ (hγK 𝔭) (hcK 𝔭)
  choose LK hLK' using hLK

  have hbca : ∀ 𝔭, IsBaseChangeAlong (φ 𝔭) (X.toGradedCartierModuleData j hc)
      ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)) (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) :=
    fun 𝔭 => CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p j (φ 𝔭) X γ hγ hc (hcK 𝔭)
  have hLL : ∀ 𝔭 (x : (X.toGradedCartierModuleData j hc).M),
      LK 𝔭 (CartierModule.baseChange (Φ := X.F) (φ 𝔭) x) =
        (X.toGradedCartierModuleData j hc).nMap ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭))
          (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭).2.2.1 (hbca 𝔭).2.2.2.1 (L x) :=
    fun 𝔭 => CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent p j (φ 𝔭) hpSnil (hpKnil 𝔭)
      (X.toGradedCartierModuleData j hc) hD ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)) (hDK 𝔭)
      (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭) L hL (LK 𝔭) (hLK' 𝔭)

  have hz : ∀ 𝔭, (X.toGradedCartierModuleData j hc).nMap ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭))
      (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭).2.2.1 (hbca 𝔭).2.2.2.1 ζ = 0 := by
    intro 𝔭
    have hmaps : (X.toGradedCartierModuleData j hc).nMap ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭))
        (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭).2.2.1 (hbca 𝔭).2.2.2.1 ζ ∈
        ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).eta (LK 𝔭) (hLK' 𝔭).isCartierLMap.map_verschiebung := by
      obtain ⟨⟨x, x'⟩, rfl⟩ := (X.toGradedCartierModuleData j hc).nMk_surjective ζ
      rw [mem_eta_iff] at hζ ⊢
      calc ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).phi (LK 𝔭) (hLK' 𝔭).isCartierLMap.map_verschiebung
            ((X.toGradedCartierModuleData j hc).nMap ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭))
              (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭).2.2.1 (hbca 𝔭).2.2.2.1 ((X.toGradedCartierModuleData j hc).nMk (x, x')))
          = (X.toGradedCartierModuleData j hc).nMap ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭))
              (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭).2.2.1 (hbca 𝔭).2.2.2.1 (L x) +
            ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭)).nMk (CartierModule.baseChange (Φ := X.F) (φ 𝔭) x', 0) := by
            rw [nMap_nMk, phi_nMk]; erw [hLL 𝔭 x]; rfl
        _ = (X.toGradedCartierModuleData j hc).nMap ((X.map (φ 𝔭)).toGradedCartierModuleData ((φ 𝔭).comp j) (hcK 𝔭))
              (CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (hbca 𝔭).2.2.1 (hbca 𝔭).2.2.2.1
              (L x + (X.toGradedCartierModuleData j hc).nMk (x', 0)) := by
              rw [map_add, nMap_nMk, map_zero]; rfl
        _ = _ := by rw [← phi_nMk _ L hL.isCartierLMap.map_verschiebung, hζ]
    exact CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed p ((φ 𝔭).comp j)
      (X.map (φ 𝔭)) _ (hγK 𝔭) (hcK 𝔭) (LK 𝔭) (hLK' 𝔭) _ hmaps (by rw [← map_nsmul, hp, map_zero])

  exact CerednikDrinfeld.FormalODModule.eq_zero_of_forall_nMap_baseChange_eq_zero p j X γ hγ hc K φ
    (fun s hs => eq_zero_of_forall_geomPt_eq_zero s hs) hcK
    (fun 𝔭 => CartierModule.baseChange (Φ := X.F) (φ 𝔭)) (fun 𝔭 => rfl)
    (fun 𝔭 => (hbca 𝔭).2.2.1) (fun 𝔭 => (hbca 𝔭).2.2.2.1) ζ hz

end S_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced (solution)
