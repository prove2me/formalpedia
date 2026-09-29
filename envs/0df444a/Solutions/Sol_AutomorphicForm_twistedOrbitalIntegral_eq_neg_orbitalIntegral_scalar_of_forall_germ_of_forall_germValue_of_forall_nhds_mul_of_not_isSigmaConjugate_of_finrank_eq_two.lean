-- Prove2me | solution 1 for AutomorphicForm.twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_forall_germ_of_forall_germValue_of_forall_nhds_mul_of_not_isSigmaConjugate_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/077bc076-5b47-5540-90f8-aec4485ce8e0

import Definitions.Def_AutomorphicForm_TwistedOrbital

import Theorems.Thm_AutomorphicForm_exists_ellipticTransport_coupled_and_weilConst_mul_eq_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_forall_germ_of_forall_germValue_of_forall_nhds_mul_of_not_isSigmaConjugate_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ∃ c : (v.adicCompletion K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (hnorm : letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
      letI := AutomorphicForm.localCentralizerBorel K v γ
      τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} +
          τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (hgerm : ∀ (c : (v.adicCompletion K)ˣ),
      ∃ ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ,
        ∀ (γ₀ : GL (Fin 2) (v.adicCompletion K)), AutomorphicForm.IsRegularSemisimple γ₀ →
        ∀ (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)),
        ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),

          (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
              ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
                @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
                @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                    Subtype.val τ = νT →
                ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                  I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f) ∧

          (((γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
              (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) →
            (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
                (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                  Subtype.val νT)) →
            A = 0 ∧
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ → B γ ≠ 0) ∧

          ((∀ g : GL (Fin 2) (v.adicCompletion K),
              ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
                 ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) →
            (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀)
                (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
                  Subtype.val νT)) →
            A ≠ 0))
    (hval : ∀ (c : (v.adicCompletion K)ˣ)
      (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
      (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
        ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
           ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
      (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
      (_hνT : ∃ τ₀ : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τ₀ ∧
        @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
          Subtype.val τ₀ = νT)
      (ν : (GL (Fin 2) (v.adicCompletion K) → ℂ) → ℂ) (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ)
      (_hgerm : ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
            letI := AutomorphicForm.localGLBorel K v
            ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
              ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
              ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
                @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
                @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                    Subtype.val τ = νT →
                ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
                  I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) + B γ * ν f),
      letI := AutomorphicForm.localGLBorel K v
      ((∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
        A * ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ)
          = -(1 : ℂ) / (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) ∧
      ((¬ ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) →
        A * ((νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal : ℂ)
          = -(2 : ℂ) / (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)))
    (hlim : ∀ (c : (v.adicCompletion K)ˣ)
      (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
      (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
      (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
      (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
      (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
      (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS),
      ∃ ρ : ℝ, 0 < ρ ∧
        (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
               AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
           (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
             ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
               ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                   AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
                 w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                   ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
          (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
           ∫ t, w t ∂τ' = ρ)) ∧
        ∀ (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ), AutomorphicForm.IsSemiLocalTestFn K L v φv →
          ∃ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ u ∈ V,
            u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) →
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) →
            ∀ (τu : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u * δ))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)) τu →
              (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K);
                letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ);
                letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _;
                Measure.map Subtype.val τu = Measure.map Subtype.val τS) →
              ∀ J I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (u * δ) τu φv J →
                AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I → J = (ρ : ℂ) * I) :
    ∀ (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ), AutomorphicForm.IsSemiLocalTestFn K L v φv →
    ∀ (fv : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v fv →
      AutomorphicForm.AreMatchingLocal K L v σ φv fv →
      ∀ I I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' →
        AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I' = (-1 : ℂ) * I := by
  intro φv hφv fv hfv hmatch I I' hI' hI
  classical
  obtain ⟨c, rfl⟩ := hγ
  have hδN : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ := ⟨y, hδ⟩

  obtain ⟨u₀, γ₀, y₁, τS, τT, hu₀, hγ₀, hell, hγ₀N, hτS, hτT, happrox, hweil, hθ, hUfin⟩ :=
    AutomorphicForm.exists_ellipticTransport_coupled_and_weilConst_mul_eq_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδN hδq τ' hτ'

  obtain ⟨ν, hν⟩ := hgerm c
  have hνfv : ν fv = 0 :=
    AutomorphicForm.germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδN hδq φv fv hfv hmatch ν hν

  obtain ⟨A, B, hG, -, -⟩ := hν γ₀ hγ₀
    (@Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v) Subtype.val τT)
  obtain ⟨W, hW, hGW⟩ := hG fv hfv

  obtain ⟨ρ, hρ0, hρW, hρ⟩ := hlim c δ hδN hδq τ' hτ' u₀ τS hτS
  obtain ⟨V, hV, hρV⟩ := hρ φv hφv

  obtain ⟨u, huV, huS, hureg, γ', hγ'W, hγ'T, hγ'reg, hconj, τγ, τu, hτγ, hτu, hmapγ, hmapu, hcoup, hTOI⟩ :=
    happrox W hW V hV
  obtain ⟨J, hJ⟩ := hTOI φv hφv
  obtain ⟨Iγ, hIγ⟩ := @AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
    K _ _ v γ' hγ'reg τγ hτγ fv hfv

  have hJI : J = Iγ := hmatch.1 (u * δ) hureg γ' hγ'reg y₁ hconj τγ τu hτγ hτu hcoup Iγ J hJ hIγ
  have hJρ : J = (ρ : ℂ) * I' := hρV u huV huS hureg τu hτu hmapu J I' hJ hI'
  have hIγ_eq := hGW γ' hγ'W hγ'T hγ'reg τγ hτγ hmapγ Iγ hIγ
  rw [hνfv, mul_zero, add_zero] at hIγ_eq

  have key : A * fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = (ρ : ℂ) * I' := by
    rw [← hIγ_eq, ← hJI, hJρ]

  have hv := hval c γ₀ hγ₀ hell _ ⟨τT, hτT, rfl⟩ ν A B hG
  have hw := hweil ρ hρW

  have hOI := AutomorphicForm.mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar K v
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ⟨c, rfl⟩ τ hτ fv I hI
  clear hGW hIγ_eq hIγ hJ hTOI hcoup hmapu hmapγ hρV hρ hρW hG hν happrox hgerm hval hlim hmatch hI hI' hconj

  set θ : ℝ := ((@Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) (AutomorphicForm.localGLBorel K v)
    Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal with hθ_def
  set Uv : ENNReal := (τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}) with hUv_def
  set Tv : ENNReal := (τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}) with hTv_def

  have hq1 : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    omega
  have hqR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast hq1

  have hTv_fin : Tv < ⊤ := by
    have : Tv ≤ Uv * (Ideal.absNorm v.asIdeal : ENNReal) := by rw [hnorm]; exact le_self_add
    exact lt_of_le_of_lt this (ENNReal.mul_lt_top hUfin (ENNReal.natCast_lt_top _))
  have hvol : Tv.toReal = Uv.toReal * ((Ideal.absNorm v.asIdeal : ℕ) - 1 : ℝ) := by
    have h := congrArg ENNReal.toReal hnorm
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hTv_fin.ne hUfin.ne, ENNReal.toReal_natCast] at h
    linarith

  have hU : ∀ r : ℝ, ((r : ℝ) : ℂ) = (r : ℂ) := fun r => rfl
  have hθ0 : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hcase : A * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) * (Uv.toReal : ℂ) = -(ρ : ℂ) := by
    have hq0 : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) ≠ 0 := by
      have : ((1 : ℝ) : ℂ) ≠ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast hqR.ne
      intro h; apply this; push_cast; linear_combination (-1 : ℂ) * h
    by_cases hR : ∃ t ∈ AutomorphicForm.localCentralizer K v γ₀,
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)
    · have h1 := hv.1 hR
      have h2 : (ρ : ℂ) * (θ : ℂ) = (Uv.toReal : ℂ) := by exact_mod_cast hw.1 hR

      have h1' : A * (θ : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) = -1 := by
        rw [h1]; field_simp
      calc A * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) * (Uv.toReal : ℂ)
          = (A * (θ : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) * (ρ : ℂ) := by rw [← h2]; ring
        _ = -(ρ : ℂ) := by rw [h1']; ring
    · have h1 := hv.2 hR
      have h2 : (ρ : ℂ) * (θ : ℂ) = 2 * (Uv.toReal : ℂ) := by exact_mod_cast hw.2 hR
      have h1' : A * (θ : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) = -2 := by
        rw [h1]; field_simp
      have h2' : (Uv.toReal : ℂ) = (ρ : ℂ) * (θ : ℂ) / 2 := by rw [h2]; ring
      calc A * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1) * (Uv.toReal : ℂ)
          = (A * (θ : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) * (ρ : ℂ) / 2 := by rw [h2']; ring
        _ = -(ρ : ℂ) := by rw [h1']; ring

  have hI : I * ((Uv.toReal : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) - 1)) =
      fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [← hOI, hvol]; push_cast; ring

  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hsum : (ρ : ℂ) * (I' + I) = 0 := by
    linear_combination key.symm - A * hI + I * hcase
  rcases mul_eq_zero.mp hsum with h | h
  · exact absurd h hρC
  · linear_combination h

end S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_forall_germ_of_forall_germValue_of_forall_nhds_mul_of_not_isSigmaConjugate_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_forall_germ_of_forall_germValue_of_forall_nhds_mul_of_not_isSigmaConjugate_of_finrank_eq_two (solution)
