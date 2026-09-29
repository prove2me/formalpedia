-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/54ca5161-fa82-503a-88d3-8da3a38b103d

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isIsogenyOfHeight_map_node_rigidNum_single_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm MvFormalGroup.CartierModule.instModulePadicInt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq"
p2m_attr_erase "simp" "CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace B30ER

variable (p : ℕ) [Fact p.Prime]

theorem isField_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsField (WittVector p k ⧸ pIdeal p (WittVector p k)) := by
  obtain ⟨e⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  exact MulEquiv.isField (Field.toIsField k) e.symm.toMulEquiv

@[reducible] noncomputable def fieldQuot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Field (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
  (isField_quot p k).toField

scoped instance charP_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := by
  haveI : Nontrivial (WittVector p k ⧸ pIdeal p (WittVector p k)) := (isField_quot p k).nontrivial
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton _))

theorem exists_nodeAlgHom (k : Type) [CommRing k] :
    ∃ f₀ : EdgeFamily.edgeRingCharP p k →ₐ[k] k,
      f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0 ∧ f₀ (EdgeFamily.edgeRingCharP.η p k) = 0 := by
  have h1 : IsUnit ((0 : k) ^ (p - 1) - 1) := by
    rw [zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt), zero_sub]; exact isUnit_one.neg
  let pt : (FormalOmega.chartE k (0 : k) p).obj k := ⟨((0 : k), (0 : k)), by simp, h1, h1⟩
  exact ⟨FormalOmega.chartERing.lift pt, FormalOmega.chartERing.lift_ξ pt, FormalOmega.chartERing.lift_η pt⟩

scoped instance isNoetherianRing_edgeRingCharP (k : Type) [CommRing k] [IsNoetherianRing k] :
    IsNoetherianRing (EdgeFamily.edgeRingCharP p k) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr k (0 : k) p)) _
    (show IsNoetherianRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {FormalOmega.edgeRel k (0 : k)}) from inferInstance)

section nodefibre

variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem nodeFibre [CharP R p] (j : Zp2 p →+* EdgeFamily.edgeRingCharP p R)
    (f₀ : EdgeFamily.edgeRingCharP p R →ₐ[R] R)
    (hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p R) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p R) = 0)
    (hj : (algebraMap R (EdgeFamily.edgeRingCharP p R)).comp (f₀.toRingHom.comp j) = j)
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p R)) (hX4 : X.HasHeight 4)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p R)) :
    ((X.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))).IsHomogeneousVBasis j
        (fun i => baseChange (algebraMap R (EdgeFamily.edgeRingCharP p R)) (baseChange f₀.toRingHom (γ i))) ∧
    ((X.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))).HasStructureConstants
        (fun i => baseChange (algebraMap R (EdgeFamily.edgeRingCharP p R)) (baseChange f₀.toRingHom (γ i)))
        (EdgeFamily.edgeConstants p (0 : EdgeFamily.edgeRingCharP p R) 0) ∧
    ((X.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))).IsSpecial j ∧
    ((X.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))).HasHeight 4 := by
  have hb0 := (hγ.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))
  have hb : ((X.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))).IsHomogeneousVBasis j
      (fun i => baseChange (algebraMap R (EdgeFamily.edgeRingCharP p R)) (baseChange f₀.toRingHom (γ i))) := by
    convert hb0 using 2
    exact hj.symm
  have hc := (hγa.map f₀.toRingHom).map (algebraMap R (EdgeFamily.edgeRingCharP p R))
  have hconst : (fun m i => algebraMap R (EdgeFamily.edgeRingCharP p R) (f₀.toRingHom (EdgeFamily.edgeRingConstants p R m i))) =
      EdgeFamily.edgeConstants p (0 : EdgeFamily.edgeRingCharP p R) 0 := by
    funext m i
    rw [EdgeFamily.edgeRingConstants, EdgeFamily.edgeConstants_map, EdgeFamily.edgeConstants_map]
    show EdgeFamily.edgeConstants p (algebraMap R _ (f₀ (EdgeFamily.edgeRingCharP.ξ p R)))
      (algebraMap R _ (f₀ (EdgeFamily.edgeRingCharP.η p R))) m i = _
    rw [hf₀ξ, hf₀η, map_zero]
  rw [hconst] at hc
  refine ⟨hb, hc, ?_, ?_⟩
  · refine CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis p j ?_ _ _ hb
    have hp0 : (p : EdgeFamily.edgeRingCharP p R) = 0 := by
      rw [← map_natCast (algebraMap R (EdgeFamily.edgeRingCharP p R)), CharP.cast_eq_zero, map_zero]
    rw [hp0, Ideal.span_singleton_eq_bot.mpr rfl]
    exact ⟨fun x hx => by simpa [SModEq.sub_mem] using hx 1⟩
  · have h1 := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f₀.toRingHom (X.act (p : Zp2 p)) (X.isLawHom_act _).1 hX4
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (algebraMap R (EdgeFamily.edgeRingCharP p R))
      ((X.map f₀.toRingHom).act (p : Zp2 p)) ((X.map f₀.toRingHom).isLawHom_act _).1 h1

end nodefibre

section adm

variable (k : Type) [Field k] [CharP k p] [PerfectRing k p]

local notation "𝕆" => WittVector p k
local notation "kb" => WittVector p k ⧸ pIdeal p (WittVector p k)
local notation "E₁" => EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))

noncomputable abbrev ψE : WittVector p k →+* EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
  (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
    (Ideal.Quotient.mk (pIdeal p (WittVector p k)))

noncomputable abbrev gE : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸
    pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) :=
  (Ideal.Quotient.mk _).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)

omit [CharP k p] [PerfectRing k p] in
theorem residueMap_ψE : residueMap (p := p) (ψE p k) = gE p k := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

theorem admissible (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (f₀ : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →ₐ[WittVector p k ⧸ pIdeal p (WittVector p k)]
      (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hXs : X.IsSpecial (structureMap ι (ψE p k))) (hX4 : X.HasHeight 4)
    (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀.toRingHom) ρ₀ (4 * m))
    (ρ₁ : FormalODModule.Hom ((X.map f₀.toRingHom).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)) X)
    (hρ₁ : FormalODModule.IsIsogenyOfHeight ((X.map f₀.toRingHom).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)) X ρ₁.toSeries 4) :
    (Rigidified.mk (Φ := Φ) X (m + 1)
      ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p _))).comp (ρ₀.map (gE p k)))).IsAdmissible ι (ψE p k) := by
  letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := fieldQuot p k
  refine ⟨hXs, hX4, ?_⟩
  show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (ψE p k))) (X.map (Ideal.Quotient.mk (pIdeal p _)))
    ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p _))).comp (ρ₀.map (gE p k))) (4 * (m + 1))
  rw [residueMap_ψE]
  have h1 : FormalODModule.IsODHom ((X.map f₀.toRingHom).map (gE p k)) (X.map (Ideal.Quotient.mk (pIdeal p _)))
      (ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p _))) := by
    have h := ρ₁.isODHom.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))
    rw [FormalODModule.map_map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)
      (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (X.map f₀.toRingHom)] at h
    exact h
  refine ⟨h1.comp (hρ₀.1.map (gE p k)), ?_⟩
  have d0 : FormalODModule.HasKernelOfDegree (ρ₀.map (gE p k)) (p ^ (4 * m)) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (gE p k) ρ₀ hρ₀.1.1.1 hρ₀.2
  have d1 : FormalODModule.HasKernelOfDegree (ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p _))) (p ^ 4) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ₁.toSeries ρ₁.isODHom.1.1 hρ₁.2
  rw [show p ^ (4 * (m + 1)) = p ^ (4 * m) * p ^ 4 by ring]
  exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp (hρ₀.1.map (gE p k)).1.1 h1.1.1 d0 d1

end adm

end B30ER
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants.B30ER"

open B30ER in

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
    :
    ∀ (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F),
      X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ →
      X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))) →
      X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) → X.HasHeight 4 →
    ∃ (n : ℕ) (ρ : Series ((EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) ⧸ pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))),
      (Rigidified.mk (Φ := Φ) X n ρ).IsAdmissible ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* Ω),
        ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
          ((Rigidified.mk (Φ := Φ) X n ρ).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
        (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q ∧ Q.IsQuadrupleOf d ∧
          d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]]
              stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 +
              (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap := by
  intro X γ hγ hγa hXs hX4
  classical
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := B30ER.fieldQuot p k

  obtain ⟨f₀, hf₀ξ, hf₀η⟩ := B30ER.exists_nodeAlgHom p (WittVector p k ⧸ pIdeal p (WittVector p k))
  have hj : (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (f₀.toRingHom.comp (structureMap ι (B30ER.ψE p k))) = structureMap ι (B30ER.ψE p k) := by
    refine RingHom.ext fun x => ?_
    simp only [structureMap, B30ER.ψE, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  obtain ⟨hδ, hδa, hYs, hY4⟩ := B30ER.nodeFibre p (structureMap ι (B30ER.ψE p k)) f₀ hf₀ξ hf₀η hj X hX4 γ hγ hγa

  obtain ⟨ρ₁, hρ₁0, hρ₁1, hρ₁h⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants
      p (WittVector p k ⧸ pIdeal p (WittVector p k)) (structureMap ι (B30ER.ψE p k)) _ X hYs hY4 hXs hX4 _ hδ hδa γ hγ hγa

  have hf₀ : f₀.toRingHom.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id _ := f₀.comp_algebraMap
  obtain ⟨m, ρ₀, hρ₀, hOD₀, hcb, hcΦg, a, hN⟩ := CerednikDrinfeld.FormalODModule.exists_isIsogenyOfHeight_map_node_rigidNum_single_eq
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀.toRingHom hf₀ hf₀ξ hf₀η
  refine ⟨m + 1, ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))))), B30ER.admissible p k ι Φ f₀ X hXs hX4 m ρ₀ hρ₀ ρ₁ hρ₁h, ?_⟩

  exact CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_line_eq_of_rigidNum_single_eq_of_edge_isogeny
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀.toRingHom hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN ρ₁ hρ₁0 hρ₁1 hρ₁h

end S_CerednikDrinfeld_FormalODModule_forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_forall_exists_isAdmissible_forall_isCartierQuadruple_map_line_eq_of_hasStructureConstants_edgeRingConstants (solution)
