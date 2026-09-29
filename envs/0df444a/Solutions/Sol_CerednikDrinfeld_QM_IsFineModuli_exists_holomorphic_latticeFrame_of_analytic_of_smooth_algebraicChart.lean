-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/48bba4c2-479c-58ec-9121-03585c240217

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_latticeBasis_of_uniformization_family_of_smooth
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_frameCoords_of_uniformization_family_of_smooth
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

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

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (j : Spec (CommRingCat.of Sc) ⟶ M) [IsOpenImmersion j]
    (hj : j ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc)))

    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t)) :
    ∃ (ε : ℝ) (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (κ : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
      (A : ℍ[ℚ, a, b] → Fin 4 → Fin 4 → ℤ) (T : Set (Fin 4 → ℤ)) (a₀ : Fin 4 → ℤ),
      0 < ε ∧ ε ≤ r ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0) ∧

      (∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε →
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM,
          x.1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j →
          ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)) = x) ∧

      (∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball (σ₀ t) ε)) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε,
        (∀ i : Fin 4, v i z ∈ κ z • latt (u z).1) ∧
        ∀ x ∈ κ z • latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε, ∀ lam ∈ Λ, ∀ j₀ : Fin 4,
        ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z) = ∑ i, (A lam i j₀ : ℂ) • v i z) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε, ∀ w : Fin 2 → ℂ,
        (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
            FactorsThrough (u z).1.lev P ∧ e (u z).1 P = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
          ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) =
            (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε,
        e (u z).1 (u z).2.P =
          (((κ z)⁻¹ • (((m : ℂ)⁻¹) • ∑ i, (a₀ i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) := by
  classical

  let sSc : Spec (CommRingCat.of Sc) ⟶ Spec (CommRingCat.of ℂ) := Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))
  obtain ⟨𝒰𝒜, h𝒰𝒜⟩ := hM.ptF_surjective Sc sSc ⟨j, hj⟩

  have hfib : ∀ σ : Sc →ₐ[ℂ] ℂ, ∃ (uσ : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (gσ : uσ.1.A ⟶ 𝒰𝒜.1.A)
      (hc : CategoryTheory.IsPullback gσ uσ.1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom))),
      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uσ.1.f),
        (uσ.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ gσ =
          (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
            ⟨P.1 ≫ gσ, by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gσ, by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, uσ.1.act x ≫ gσ = gσ ≫ 𝒰𝒜.1.act x) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uσ.1.f,
        FactorsThrough uσ.1.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.C, P₀ ≫ 𝒰𝒜.1.lev = P.1 ≫ gσ) ∧
      (uσ.2.P).1 ≫ gσ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1 ∧
      FakeEllipticCurve.WithFullLevel.IsPullback σ.toRingHom 𝒰𝒜 uσ := by
    intro σ
    obtain ⟨uσ, hpb⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback σ.toRingHom 𝒰𝒜
    obtain ⟨gσ, hg, hmul, hact', hlev', hP⟩ := hpb
    exact ⟨uσ, gσ, hg, fun P Q => hmul _ P Q, hact', fun P hP' => hlev' _ P hP', hP, ⟨gσ, hg, hmul, hact', hlev', hP⟩⟩
  choose uOf gOf hcart hmulσ hact hlev hgen hwpb using hfib

  haveI : Nonempty (Sc →ₐ[ℂ] ℂ) := ⟨σ₀⟩
  let σz : ℂ → (Sc →ₐ[ℂ] ℂ) := fun z => Function.invFunOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 z
  have hσz : ∀ σ ∈ 𝒰, σz (σ t) = σ := fun σ hσ => hbij.injOn.leftInvOn_invFunOn hσ
  let u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ := fun z => uOf (σz z)
  let g : ∀ z : ℂ, (u z).1.A ⟶ 𝒰𝒜.1.A := fun z => gOf (σz z)
  have hg5 : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (u (σ t)).1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),
      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f),
        ((u (σ t)).1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
          (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
            ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, (u (σ t)).1.act x ≫ g (σ t) = g (σ t) ≫ 𝒰𝒜.1.act x) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f,
        FactorsThrough (u (σ t)).1.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.C, P₀ ≫ 𝒰𝒜.1.lev = P.1 ≫ g (σ t)) ∧
      ((u (σ t)).2.P).1 ≫ g (σ t) = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1 := by
    intro σ hσ
    have key : ∀ τ : Sc →ₐ[ℂ] ℂ, τ = σ →
        ∃ hc : CategoryTheory.IsPullback (gOf τ) (uOf τ).1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),
        (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (uOf τ).1.f),
          ((uOf τ).1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ gOf τ =
            (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
              ⟨P.1 ≫ gOf τ, by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ gOf τ, by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
        (∀ x : ↥Λ, (uOf τ).1.act x ≫ gOf τ = gOf τ ≫ 𝒰𝒜.1.act x) ∧
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (uOf τ).1.f,
          FactorsThrough (uOf τ).1.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.C, P₀ ≫ 𝒰𝒜.1.lev = P.1 ≫ gOf τ) ∧
        ((uOf τ).2.P).1 ≫ gOf τ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1 := by
      rintro τ rfl; exact ⟨hcart _, hmulσ _, hact _, hlev _, hgen _⟩
    exact key (σz (σ t)) (hσz σ hσ)
  have hg3 : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (u (σ t)).1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),
      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f),
        ((u (σ t)).1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
          (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
            ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, (u (σ t)).1.act x ≫ g (σ t) = g (σ t) ≫ 𝒰𝒜.1.act x) := by
    intro σ hσ
    obtain ⟨hc, h1, h2, -, -⟩ := hg5 σ hσ
    exact ⟨hc, h1, h2⟩

  obtain ⟨ε₁, κ, hε₁, hε₁r, hκ, hRELAN, hRELCOV, hKCL, hRELSURJ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic
      hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol 𝒰𝒜.1 (fun z => (u z).1) g hg3

  obtain ⟨ε₂, v, hε₂, hε₂₁, hv, hbasis⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_latticeBasis_of_uniformization_family_of_smooth
      hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol 𝒰𝒜.1 (fun z => (u z).1) g hg3 ε₁ κ hε₁ hε₁r hκ hRELAN hRELCOV hKCL

  obtain ⟨ε₃, A, T, a₀, hε₃, hε₃₂, hLAM, hLEVN, hLEVM⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_frameCoords_of_uniformization_family_of_smooth
      hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol m 𝒰𝒜 u g hg5 ε₁ κ hε₁ hε₁r hκ hRELAN hRELCOV hKCL hRELSURJ ε₂ v hε₂ hε₂₁ hv hbasis
  have hball₃₁ : Metric.ball (σ₀ t) ε₃ ⊆ Metric.ball (σ₀ t) ε₁ :=
    (Metric.ball_subset_ball hε₃₂).trans (Metric.ball_subset_ball hε₂₁)

  refine ⟨ε₃, u, fun z => (κ z)⁻¹, v, A, T, a₀, hε₃, hε₃₂.trans (hε₂₁.trans hε₁r), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz
    exact inv_ne_zero (hκ z (hball₃₁ hz))
  ·
    intro σ hσ hz x hx
    have hwpb' : FakeEllipticCurve.WithFullLevel.IsPullback σ.toRingHom 𝒰𝒜 (u (σ t)) := by
      have key : ∀ τ : Sc →ₐ[ℂ] ℂ, τ = σ → FakeEllipticCurve.WithFullLevel.IsPullback σ.toRingHom 𝒰𝒜 (uOf τ) := by
        rintro τ rfl; exact hwpb _
      exact key (σz (σ t)) (hσz σ hσ)
    have hsσ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ sSc = 𝟙 (Spec (CommRingCat.of ℂ)) := by
      have hc : CommRingCat.ofHom (algebraMap ℂ Sc) ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 (CommRingCat.of ℂ) := by
        ext x; simp
      show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc)) = 𝟙 _
      rw [← Spec.map_comp, hc, Spec.map_id]
    have h1 := hM.ptF_pullback Sc ℂ σ.toRingHom sSc (𝟙 _) hsσ 𝒰𝒜 (u (σ t)) hwpb'
    rw [h𝒰𝒜] at h1
    exact Subtype.ext (h1.trans hx.symm)
  ·
    intro i
    exact (hv i).mono (Metric.ball_subset_ball hε₃₂)
  ·
    intro z hz
    have hz₂ : z ∈ Metric.ball (σ₀ t) ε₂ := Metric.ball_subset_ball hε₃₂ hz
    have hκz : κ z ≠ 0 := hκ z (hball₃₁ hz)
    obtain ⟨hb₁, hb₂⟩ := hbasis z hz₂
    refine ⟨fun i => ?_, fun x hx => ?_⟩
    · have h := Submodule.smul_mem_pointwise_smul (κ z • v i z) (κ z)⁻¹ (latt (u z).1) (hb₁ i)
      rwa [smul_smul, inv_mul_cancel₀ hκz, one_smul] at h
    · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x (κ z)⁻¹ (latt (u z).1)).1 hx
      exact hb₂ y hy
  ·
    intro z hz lam hlam j₀
    exact hLAM z hz lam hlam j₀
  ·
    intro z hz w
    simp only [inv_inv]
    exact hLEVN z hz w
  ·
    intro z hz
    simp only [inv_inv]
    exact hLEVM z hz

end S_CerednikDrinfeld_QM_IsFineModuli_exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart (solution)
