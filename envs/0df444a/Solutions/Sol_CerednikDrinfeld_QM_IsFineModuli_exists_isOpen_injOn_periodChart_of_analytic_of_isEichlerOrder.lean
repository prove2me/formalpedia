-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/afcf6832-1446-504f-93e3-cc819196b867

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
import Theorems.Thm_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_differentiableOn_smul_span_eq_qmPeriodLattice_of_latticeFrame
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_injOn_periodFunction_of_latticeFrame_of_analytic
import Theorems.Thm_Complex_isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_levelModule
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_smul_eq_qmPeriodLattice_pair_of_forall_mulVec_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelModule_unique
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_of_pointEquiv
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn
import Theorems.Thm_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators
open Opposite

namespace Law4

theorem relIndex_smul {c : ℂ} (hc : c ≠ 0) (A B : Submodule ℤ (Fin 2 → ℂ)) :
    (c • A).toAddSubgroup.relIndex (c • B).toAddSubgroup = A.toAddSubgroup.relIndex B.toAddSubgroup := by
  have hinj : Function.Injective (DistribSMul.toLinearMap ℤ (Fin 2 → ℂ) c) :=
    fun x y h => smul_right_injective (Fin 2 → ℂ) hc h
  rw [Submodule.pointwise_smul_def, Submodule.pointwise_smul_def, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

theorem smul_full {c : ℂ} (hc : c ≠ 0) {L : Submodule ℤ (Fin 2 → ℂ)}
    (h : ∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range b₀)) :
    ∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), c • L = Submodule.span ℤ (Set.range b₀) := by
  obtain ⟨b₀, rfl⟩ := h
  let eC : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 → ℂ) := (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) c hc).restrictScalars ℝ
  refine ⟨b₀.map eC, ?_⟩
  rw [Submodule.pointwise_smul_def, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, Module.Basis.map_apply]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨b₀ i, ⟨i, rfl⟩, rfl⟩

end Law4

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)

    (m : ℕ) (hm : 3 ≤ m) (hmc : m.Coprime (N * q * q'))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)
    (σ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM) :
    ∃ (W : Set UpperHalfPlane) (_ : IsOpen W) (h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM),
      σ₀ ∈ h '' W ∧ Set.InjOn h W ∧

      (∀ (U : M.Opens) (s : Γ(M, U)),
        IsOpen {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F
          {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∀ (z : ℂ), 0 < z.im → UpperHalfPlane.ofComplex z ∈ W →
          ∀ hU : ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U,
            F z = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h (UpperHalfPlane.ofComplex z)).1.appLE U ⊤ hU) s)) ∧

      (∀ τ ∈ W, ∀ u : FakeEllipticCurve.WithFullLevel Λ N m ℂ,
        ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) u = h τ →
        ∃ c : ℂ, c ≠ 0 ∧ c • latt u.1 = qmPeriodLattice ι Λ τ ∧

          ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))) := by
  classical

  obtain ⟨U, hU, hσU, instU, halg, hdom, hft, hsmU, hrankU, σc, t, hσc, hdt⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
      M πM hsm σ₀.1 σ₀.2
  letI instAlg : Algebra ℂ ↑(M.presheaf.obj (op U)) := instU
  haveI : IsDomain ↑(M.presheaf.obj (op U)) := hdom
  haveI : Algebra.FiniteType ℂ ↑(M.presheaf.obj (op U)) := hft

  obtain ⟨r, 𝒰, hr, hσc𝒰, hbij, hhol, hUopen⟩ :=
    Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
      (↑(M.presheaf.obj (op U))) hsmU hrankU σc t hdt

  let j : Spec (CommRingCat.of ↑(M.presheaf.obj (op U))) ⟶ M := hU.fromSpec
  haveI hjOpen : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  have hj : j ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap ℂ ↑(M.presheaf.obj (op U)))) := by
    have hle : U ≤ πM ⁻¹ᵁ ⊤ := by simp
    have halg' : CommRingCat.ofHom (algebraMap ℂ ↑(M.presheaf.obj (op U))) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ πM.appLE ⊤ U hle := by
      ext z
      change algebraMap ℂ ↑(M.presheaf.obj (op U)) z = _
      rw [halg z]
      rfl
    rw [halg', Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec πM (isAffineOpen_top _) hU hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

  obtain ⟨ε, u, κ, v, A, T, a₀, hε, hεr, hκ, hPT, hHOLv, hBASIS, hLAM, hLEVN, hLEVM⟩ :=
    CerednikDrinfeld.QM.IsFineModuli.exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart
      hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV m hm hmc M πM ptF hM hsm
      (↑(M.presheaf.obj (op U))) hsmU hrankU j hj t σc r 𝒰 hr hσc𝒰 hbij hhol
  have hz₀ : σc t ∈ Metric.ball (σc t) ε := Metric.mem_ball_self hε

  obtain ⟨J', hJ'⟩ := QuaternionAlgebra.IsEichlerOrder.exists_levelModule hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι
  have hP2 := fun E : FakeEllipticCurve Λ N ℂ =>
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv
      hB Λ hΛ ι hι hqq' hqN hq'N latt e hL1 hE1 hE2 E
  choose lattLev hLev using hP2

  have hLevUniq : ∀ J'' : Submodule ℤ ℍ[ℚ, a, b],
      (Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
        Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J'', y * x ∈ J'')) → J'' = J' :=
    fun J'' hJ'' => (QuaternionAlgebra.IsEichlerOrder.levelModule_unique hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι J' J'' hJ' hJ'').symm

  have hmemLev : ∀ (E : FakeEllipticCurve Λ N ℂ) (c : ℂ) (w : Fin 2 → ℂ),
      (∃ v : Fin 2 → ℂ, (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧ c • v = w) ↔
        w ∈ c • lattLev E := by
    intro E c w
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨v, hv, hcv⟩; exact ⟨v, ((hLev E).1 v).2 hv, hcv⟩
    · rintro ⟨v, hv, hcv⟩; exact ⟨v, ((hLev E).1 v).1 hv, hcv⟩

  have hFIB : ∀ (E : FakeEllipticCurve Λ N ℂ) (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 →
      c • latt E = qmPeriodLattice ι Λ τ →
      ((∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
          (∃ v : Fin 2 → ℂ,
            (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
              FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
            c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
          (∃ v : Fin 2 → ℂ,
            (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
              FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
            c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))) ↔
        c • lattLev E = qmPeriodLattice ι J' τ) := by
    intro E τ c hc hcL
    have hLM : qmPeriodLattice ι Λ τ ≤ c • lattLev E := by
      rw [← hcL, Submodule.pointwise_smul_def, Submodule.pointwise_smul_def]
      exact Submodule.map_mono (hLev E).2.1
    have hMN : ∀ v ∈ c • lattLev E, ((N : ℤ) • v) ∈ qmPeriodLattice ι Λ τ := by
      intro v hv
      rw [Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [smul_comm, ← hcL]
      exact Submodule.smul_mem_pointwise_smul _ c _ ((hLev E).2.2.2.1 w hw)
    have hMstab : ∀ x ∈ Λ, ∀ v ∈ c • lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ c • lattLev E := by
      intro x hx v hv
      rw [Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem_pointwise_smul _ c _ ((hLev E).2.2.1 x hx w hw)
    have hidx : (qmPeriodLattice ι Λ τ).toAddSubgroup.relIndex (c • lattLev E).toAddSubgroup = N ^ 2 := by
      rw [← hcL, Law4.relIndex_smul hc]
      exact (hLev E).2.2.2.2
    have hbr := QuaternionAlgebra.IsEichlerOrder.forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq
      hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι τ (c • lattLev E) hLM hMN hMstab hidx
    simp only [hmemLev]
    rw [hbr]
    constructor
    · rintro ⟨J'', hJ'', hM⟩
      rwa [hLevUniq J'' hJ''] at hM
    · intro h
      exact ⟨J', hJ', h⟩
  have hP5 := CerednikDrinfeld.QM.FakeEllipticCurve.iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_of_pointEquiv
    hB Λ hΛ ι hι hqq' hqN hq'N latt e hL1 hE1 hE2 hH1 hH2 hH3 lattLev hLev
  set ME := lattLev (u (σc t)).1 with hMEdef
  have hLME : latt (u (σc t)).1 ≤ ME := (hLev _).2.1
  have hMEstab := (hLev (u (σc t)).1).2.2.1
  have hMEN := (hLev (u (σc t)).1).2.2.2.1
  have hMEidx := (hLev (u (σc t)).1).2.2.2.2
  have hspan_all : ∀ z ∈ Metric.ball (σc t) ε,
      Submodule.span ℤ (Set.range fun i : Fin 4 => v i z) = κ z • latt (u z).1 := by
    intro z hz
    obtain ⟨hmem, huniq⟩ := hBASIS z hz
    refine le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩
      exact hmem i
    · obtain ⟨n, hn, -⟩ := huniq x hx
      rw [← hn]
      exact Submodule.sum_mem _ fun i _ => by
        rw [Int.cast_smul_eq_zsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span ℤ (Set.range fun i : Fin 4 => v i (σc t)) = κ (σc t) • latt (u (σc t)).1 :=
    hspan_all _ hz₀
  obtain ⟨τ₀, c₀, hc₀, hc₀L, hc₀M⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_smul_eq_qmPeriodLattice_pair_of_forall_mulVec_mem
      hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι J' hJ'
      (κ (σc t) • latt (u (σc t)).1) (κ (σc t) • ME)
      (Law4.smul_full (hκ _ hz₀) (hL1 _).1)
      (fun x hx w hw => by
        rw [Submodule.mem_smul_pointwise_iff_exists] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem_pointwise_smul _ _ _ ((hL1 _).2 x hx w' hw'))
      (by rw [Submodule.pointwise_smul_def, Submodule.pointwise_smul_def]; exact Submodule.map_mono hLME)
      (fun w hw => by
        rw [Submodule.mem_smul_pointwise_iff_exists] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        rw [smul_comm]
        exact Submodule.smul_mem_pointwise_smul _ _ _ (hMEN w' hw'))
      (fun x hx w hw => by
        rw [Submodule.mem_smul_pointwise_iff_exists] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem_pointwise_smul _ _ _ (hMEstab x hx w' hw'))
      (by rw [Law4.relIndex_smul (hκ _ hz₀)]; exact hMEidx)

  obtain ⟨τ, c, y, hτhol, hchol, hτ₀, hcc₀, hnorm⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_differentiableOn_smul_span_eq_qmPeriodLattice_of_latticeFrame
      hB Λ hΛ ι hι hqq' (σc t) ε hε v hHOLv
      (fun z hz => by

        obtain ⟨b₁, hb₁⟩ := (hL1 (u z).1).1
        obtain ⟨hmem, huniq⟩ := hBASIS z hz
        have hle : (⊤ : Submodule ℝ (Fin 2 → ℂ)) ≤ Submodule.span ℝ (Set.range fun i : Fin 4 => v i z) := by
          have hb : ∀ j : Fin 4, κ z • b₁ j ∈ Submodule.span ℝ (Set.range fun i : Fin 4 => v i z) := by
            intro j
            have hj : κ z • b₁ j ∈ κ z • latt (u z).1 :=
              Submodule.smul_mem_pointwise_smul _ _ _ (by rw [hb₁]; exact Submodule.subset_span ⟨j, rfl⟩)
            obtain ⟨n, hn, -⟩ := huniq _ hj
            rw [← hn]
            exact Submodule.sum_mem _ fun i _ => by
              rw [Int.cast_smul_eq_zsmul]
              exact Submodule.smul_of_tower_mem _ (n i) (Submodule.subset_span ⟨i, rfl⟩)

          let eC : (Fin 2 → ℂ) ≃ₗ[ℝ] (Fin 2 → ℂ) := (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) (κ z) (hκ z hz)).restrictScalars ℝ
          have htop : Submodule.span ℝ (Set.range (b₁.map eC)) = ⊤ := (b₁.map eC).span_eq
          rw [← htop, Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          simpa [Module.Basis.map_apply, eC] using hb j
        have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (Fin 2 → ℂ) := by
          rw [Module.finrank_eq_card_basis b₁]
        exact ⟨basisOfTopLeSpanOfCardEqFinrank (fun i : Fin 4 => v i z) hle hcard, fun i => by simp⟩)
      A hLAM τ₀ c₀ hc₀ (by rw [hspan]; exact hc₀L)

  have hK : ∀ z ∈ Metric.ball (σc t) ε,
      (c z * κ z) • lattLev (u z).1 = qmPeriodLattice ι J' (τ z) :=
    QuaternionAlgebra.smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap ι hι J' N
      (Metric.ball (σc t) ε) (σc t) hz₀ (fun z => latt (u z).1) (fun z => lattLev (u z).1) κ c v y τ T hκ
      (fun z hz => (hnorm z hz).1) hBASIS (fun z hz w => ((hLev (u z).1).1 w).trans (hLEVN z hz w))
      (fun z hz i => (hnorm z hz).2.2 i) (by rw [hcc₀, hτ₀, mul_smul]; exact hc₀M)

  have hinj : Set.InjOn (fun z : ℂ => τ z) (Metric.ball (σc t) ε) :=
    CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic
      hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV m hm hmc M πM ptF hM hsm
      (↑(M.presheaf.obj (op U))) j hj t σc r 𝒰 hr hσc𝒰 hbij hhol
      ε hε hεr u κ v T a₀ hκ hPT hBASIS hLEVN hLEVM τ c y
      (fun z hz => (hnorm z hz).1) (fun z hz => (hnorm z hz).2.2)
  have hinjC : Set.InjOn (fun z : ℂ => ((τ z : UpperHalfPlane) : ℂ)) (Metric.ball (σc t) ε) :=
    fun z₁ hz₁ z₂ hz₂ h => hinj hz₁ hz₂ (UpperHalfPlane.ext h)
  obtain ⟨hW₀, g, hghol, hgτ, hτg⟩ :=
    Complex.isOpen_image_and_exists_differentiableOn_leftInverse_of_injOn_ball
      (fun z : ℂ => ((τ z : UpperHalfPlane) : ℂ)) (σc t) ε hε hτhol hinjC

  let W : Set UpperHalfPlane :=
    {τ' | (τ' : ℂ) ∈ (fun z : ℂ => ((τ z : UpperHalfPlane) : ℂ)) '' Metric.ball (σc t) ε}
  have hW : IsOpen W := hW₀.preimage UpperHalfPlane.continuous_coe
  haveI : Nonempty (↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ) := ⟨σc⟩
  let σof : UpperHalfPlane → (↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ) :=
    fun τ' => Function.invFunOn (fun σ : ↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ => σ t) 𝒰 (g (τ' : ℂ))
  have hσof : ∀ τ' ∈ W, σof τ' ∈ 𝒰 ∧ (σof τ') t = g (τ' : ℂ) ∧ g (τ' : ℂ) ∈ Metric.ball (σc t) ε := by
    intro τ' hτ'
    have hgε : g (τ' : ℂ) ∈ Metric.ball (σc t) ε := (hτg _ hτ').1
    have hgr : g (τ' : ℂ) ∈ Metric.ball (σc t) r := Metric.ball_subset_ball hεr hgε
    have hsurj := hbij.surjOn hgr
    exact ⟨Function.invFunOn_mem hsurj, Function.invFunOn_eq hsurj, hgε⟩
  let h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM :=
    fun τ' => ⟨Spec.map (CommRingCat.ofHom (σof τ').toRingHom) ≫ j, by
      rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id]⟩
  refine ⟨W, hW, h, ?_, ?_, ?_, ?_⟩
  ·
    have hσ₀eq : σ₀.1 = Spec.map (CommRingCat.ofHom σc.toRingHom) ≫ j := by
      have hσc' : CommRingCat.ofHom σc.toRingHom = σ₀.1.appLE U ⊤ hσU ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
        ext s
        exact hσc s
      rw [hσc', Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec σ₀.1 hU (isAffineOpen_top _) hσU,
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
        Category.id_comp]
    have hmemW : τ (σc t) ∈ W := ⟨σc t, hz₀, rfl⟩
    refine ⟨τ (σc t), hmemW, ?_⟩
    have hg₀ : g ((τ (σc t) : UpperHalfPlane) : ℂ) = σc t := hgτ _ hz₀
    have hσof₀ : σof (τ (σc t)) = σc := by
      simp only [σof, hg₀]
      exact hbij.injOn.leftInvOn_invFunOn hσc𝒰
    apply Subtype.ext
    simp only [h, hσof₀]
    exact hσ₀eq.symm
  ·
    intro τ₁ hτ₁ τ₂ hτ₂ heq
    have h1 : Spec.map (CommRingCat.ofHom (σof τ₁).toRingHom) ≫ j = Spec.map (CommRingCat.ofHom (σof τ₂).toRingHom) ≫ j :=
      congrArg Subtype.val heq
    have h2 := Spec.map_injective ((cancel_mono j).1 h1)
    have h3 : (σof τ₁) t = (σof τ₂) t := by
      have := congrArg (fun φ : CommRingCat.of ↑(M.presheaf.obj (op U)) ⟶ CommRingCat.of ℂ => φ.hom t) h2
      simpa using this
    rw [(hσof τ₁ hτ₁).2.1, (hσof τ₂ hτ₂).2.1] at h3
    have h4 : ((τ₁ : UpperHalfPlane) : ℂ) = ((τ₂ : UpperHalfPlane) : ℂ) := by
      rw [← (hτg _ hτ₁).2, ← (hτg _ hτ₂).2, h3]
    exact UpperHalfPlane.ext h4
  ·
    intro U' s
    let σfun : ℂ → (↑(M.presheaf.obj (op U)) →+* ℂ) :=
      fun w => (Function.invFunOn (fun σ : ↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ => σ t) 𝒰 w).toRingHom
    have hσfun : ∀ a : ↑(M.presheaf.obj (op U)), ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F (Metric.ball (σc t) r) ∧ ∀ w ∈ Metric.ball (σc t) r, σfun w a = F w := by
      intro a
      obtain ⟨F, hF, hFσ⟩ := hhol a
      refine ⟨F, hF, fun w hw => ?_⟩
      have hs := hbij.surjOn hw
      simp only [σfun, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hFσ _ (Function.invFunOn_mem hs), Function.invFunOn_eq hs]
    obtain ⟨hO, G, hG, hGval⟩ :=
      AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn
        M U hU (Metric.ball (σc t) r) Metric.isOpen_ball σfun hσfun U' s

    have hS : {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U'} =
        {z : ℂ | 0 < z.im} ∩ (((fun z : ℂ => ((τ z : UpperHalfPlane) : ℂ)) '' Metric.ball (σc t) ε) ∩
          g ⁻¹' {w : ℂ | w ∈ Metric.ball (σc t) r ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σfun w)) ≫ hU.fromSpec) ⁻¹ᵁ U'}) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hz, hzW, hzU⟩
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hzW hzU
        exact ⟨hz, hzW, Metric.ball_subset_ball hεr (hτg _ hzW).1, hzU⟩
      · rintro ⟨hz, hzW, -, hzU⟩
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
        exact ⟨hz, hzW, hzU⟩
    refine ⟨?_, fun z => G (g ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ)), ?_, ?_⟩
    · rw [hS]
      exact (isOpen_lt continuous_const Complex.continuous_im).inter (hghol.continuousOn.isOpen_inter_preimage hW₀ hO)
    · rw [hS]
      have hcomp : DifferentiableOn ℂ (G ∘ g)
          ((((fun z : ℂ => ((τ z : UpperHalfPlane) : ℂ)) '' Metric.ball (σc t) ε) ∩
            g ⁻¹' {w : ℂ | w ∈ Metric.ball (σc t) r ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σfun w)) ≫ hU.fromSpec) ⁻¹ᵁ U'})) :=
        hG.comp (hghol.mono Set.inter_subset_left) fun z hz => hz.2
      refine (hcomp.mono Set.inter_subset_right).congr ?_
      rintro z ⟨hz, -⟩
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    · intro z hz hzW hU'
      have hzW' : z ∈ (fun z : ℂ => ((τ z : UpperHalfPlane) : ℂ)) '' Metric.ball (σc t) ε := by
        rwa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hzW
      have hgz : g ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) ∈ Metric.ball (σc t) r := by
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
        exact Metric.ball_subset_ball hεr (hτg _ hzW').1
      exact hGval _ hgz hU'
  ·
    intro τ' hτ' u' hu'
    obtain ⟨hσ𝒰, hσt, hgε⟩ := hσof τ' hτ'
    have hτz : τ (g (τ' : ℂ)) = τ' := UpperHalfPlane.ext (hτg _ hτ').2
    have hPT' : ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (g (τ' : ℂ))) = h τ' := by
      rw [← hσt]
      exact hPT (σof τ') hσ𝒰 (by rw [hσt]; exact hgε) (h τ') rfl
    obtain ⟨eI, heI, hI1, hI2, hI3, -⟩ := hM.ptF_injective ℂ (𝟙 _) u' (u (g (τ' : ℂ))) (hu'.trans hPT'.symm)
    obtain ⟨d, hd, hdL, hdM⟩ := (hP5 u'.1 (u (g (τ' : ℂ))).1).1 ⟨eI, heI, hI1, hI2, hI3⟩
    obtain ⟨hcz, hcspan, -⟩ := hnorm _ hgε
    have hL' : (c (g (τ' : ℂ)) * κ (g (τ' : ℂ)) * d) • latt u'.1 = qmPeriodLattice ι Λ τ' := by
      rw [mul_smul, hdL, mul_smul, ← hspan_all _ hgε, hcspan, hτz]
    refine ⟨c (g (τ' : ℂ)) * κ (g (τ' : ℂ)) * d, mul_ne_zero (mul_ne_zero hcz (hκ _ hgε)) hd, hL', ?_⟩
    refine (hFIB u'.1 τ' _ (mul_ne_zero (mul_ne_zero hcz (hκ _ hgε)) hd) hL').2 ?_
    rw [mul_smul, hdM, hK _ hgε, hτz]

end S_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder (solution)
