-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0ffa8ecf-64bb-5e6a-953e-e4633bdc43dd

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Theorems.Thm_CerednikDrinfeld_FormalODModule_lattice_eq_and_ker_eq_span_of_isCartierQuadruple_map_node_of_rigidNum_single_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace B35NC

variable (p : ℕ) [Fact p.Prime]

theorem isField_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsField (WittVector p k ⧸ pIdeal p (WittVector p k)) := by
  obtain ⟨e⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  exact MulEquiv.isField (Field.toIsField k) e.symm.toMulEquiv

@[reducible] noncomputable def fieldQuot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Field (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
  (isField_quot p k).toField

theorem natCast_quot_eq_zero (k : Type) [CommRing k] : ((p : ℕ) : (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k)))]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem admissible0 (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))))
    (hX4 : X.HasHeight 4)
    (f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m)) :
    (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).IsAdmissible ι
      (Ideal.Quotient.mk (pIdeal p (WittVector p k))) := by
  letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := fieldQuot p k
  haveI : IsNoetherianRing (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k))) p)) _
      (show IsNoetherianRing (MvPolynomial (Fin 2) (WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸ Ideal.span {FormalOmega.edgeRel (WittVector p k ⧸ pIdeal p (WittVector p k)) (0 : (WittVector p k ⧸ pIdeal p (WittVector p k)))}) from inferInstance)
  refine ⟨?_, ?_, ?_⟩
  ·
    have h := CerednikDrinfeld.FormalODModule.IsSpecial.map
      (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) f₀ X hXs
    have e : f₀.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) =
        structureMap ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) := by
      refine RingHom.ext fun x => ?_
      show f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))
          (Ideal.Quotient.mk (pIdeal p (WittVector p k)) (ι x))) = Ideal.Quotient.mk (pIdeal p (WittVector p k)) (ι x)
      exact RingHom.congr_fun hf₀ _
    rw [e] at h
    exact h
  ·
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f₀ (X.act (p : Zp2 p)) (X.isLawHom_act _).1 hX4
  ·
    show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))
      ((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (4 * m)
    have e : residueMap (p := p) (Ideal.Quotient.mk (pIdeal p (WittVector p k))) = Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl)
    rw [e]
    exact ⟨hρ₀.1.map _, CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ₀ hρ₀.1.1.1 hρ₀.2⟩

end B35NC

open B35NC in
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
    :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y₀ : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* Ω),
      ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
        ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).IsCartierQuadruple ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) Q ∧
        Q.IsQuadrupleOf d ∧
        d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(0 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap := by
  intro Ω _ _ _ y₀
  classical
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  letI kbF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := B35NC.fieldQuot p k

  have hp0 : (p : Ω) = 0 := by
    have := congrArg y₀ (B35NC.natCast_quot_eq_zero p k)
    rwa [map_natCast, map_zero] at this
  haveI : CharP Ω p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  have hpn : IsNilpotent (p : Ω) := ⟨1, by rw [pow_one, hp0]⟩

  have hadm0 := B35NC.admissible0 p k ι Φ X hXs hX4 f₀ hf₀ m ρ₀ hρ₀
  have hadm := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι
    (Ideal.Quotient.mk (pIdeal p (WittVector p k))) y₀ _ hadm0

  obtain ⟨Q, hQ⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ
    (CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed p k ι Φ hΦ hcΦ)
    hrΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hpn _ hadm

  obtain ⟨d, hd0, hd1⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
    p g hg (0 : Ω) (0 : Ω) (mul_zero _) (Or.inl rfl) (Or.inl rfl)
  refine ⟨Q, d, hQ, ?_, hd0, hd1⟩

  intro x
  have hlat := CerednikDrinfeld.FormalODModule.lattice_eq_and_ker_eq_span_of_isCartierQuadruple_map_node_of_rigidNum_single_eq p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN Ω y₀ Q hQ x
  exact ((CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_eq_span_node p g hg d hd0 hd1 Q x).mpr hlat) x

end S_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq (solution)
