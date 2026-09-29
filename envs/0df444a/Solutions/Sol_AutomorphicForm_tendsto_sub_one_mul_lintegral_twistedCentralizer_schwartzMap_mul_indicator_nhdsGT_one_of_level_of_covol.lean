-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e85c96c1-8a2f-5150-8f58-35038aec37c0

import Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
import Theorems.Thm_AutomorphicForm_tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
import Theorems.Thm_AutomorphicForm_exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq
import Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
import Theorems.Thm_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option maxHeartbeats 6400000 in
open scoped Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ)) (hg : HasCompactSupport g)
    (hg' : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hS₁ : S₀ ⊆ S₁)
    (W : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hWm : ∀ v, MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (W v))
    (hW₀ : ∀ v ∉ S₁, ∀ x : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
      ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v ↔
        ∀ i j, ((x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
          AutomorphicForm.semiLocalIntegers K L v))
    (hW₁ : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S → ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          AutomorphicForm.semiLocalIntegralSet K L v) →
        U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) =
          ∏ v ∈ S, (W v).indicator (fun _ => (1 : ℂ))
            (AutomorphicForm.tensorPlace K L v (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))
    (hunit : ∀ v ∉ S₁,
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, ∀ s' : ℝ, 1 ≤ s' →
      ∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W v},
          ENNReal.ofReal (‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ^ s') ∂(τf' v) =
        Corr v s' * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s')))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s'))⁻¹))
    (hCorr₁ : ∀ v ∈ S₁, Corr v 1 ≠ ⊤ ∧ Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)))
    (hE8 :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
          ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
            X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
            Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
          ∫⁻ cc : Fin n₂ → ℝ, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L (((∑ k, cc k • e₂ k).mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re) *
        ∏ v ∈ S₁, Corr v 1 =
      (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
        2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) * ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        ∫⁻ t, ENNReal.ofReal
          (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1) *
            U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2)).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s) ∂τ')
        (𝓝[>] (1 : ℝ))
        (𝓝 (2⁻¹ * ((∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
          (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
            ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
              NumberField.dedekindZeta_residue K))))) := by
  classical
  letI algR : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI algE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  letI mB : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    borel (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
  have harch' := harch
  obtain ⟨n₂, e₂, hli, hspan, hmap⟩ := harch'

  set archcol : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → (Fin 2 → mixedEmbedding.mixedSpace L) :=
    fun X i => InfiniteAdeleRing.ringEquiv_mixedSpace L
      (AutomorphicForm.archIdent K L ((X.mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)) with harchcol
  set Dinf : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) = ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} with hDinf
  set G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞ :=
    Dinf.indicator (fun X => ENNReal.ofReal (g (archcol X)).re) with hG

  haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  haveI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
  have hcontE : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace L) := by
    refine Continuous.congr ?_ (fun x => (InfiniteAdeleRing.ringEquiv_mixedSpace_apply L x).symm)
    refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
        (continuous_apply _)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
        (continuous_apply _)
  have hcontI : Continuous (AutomorphicForm.archIdent K L) :=
    (AutomorphicForm.archIdentHomeomorph K L).continuous
  have hcontA : Continuous archcol := by
    simp only [harchcol]
    refine continuous_pi fun i => hcontE.comp (hcontI.comp ?_)
    exact (continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)
  have hDclosed : IsClosed Dinf := by
    simp only [hDinf]
    exact AutomorphicForm.isClosed_twistedCommutant K L (InfiniteAdeleRing K) σ _
  have hGm : Measurable[borel _] G := by
    simp only [hG]
    refine Measurable.indicator ?_ hDclosed.measurableSet
    exact (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (g.continuous.comp hcontA))).measurable

  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ y, ‖g y‖ ≤ Cb :=
    ⟨‖g.toBoundedContinuousFunction‖, fun y => by
      simpa using g.toBoundedContinuousFunction.norm_coe_le_norm y⟩
  have hGC : ∀ X, G X ≤ ENNReal.ofReal Cb := by
    intro X
    simp only [hG]
    refine Set.indicator_apply_le' (fun _ => ?_) (fun _ => zero_le)
    exact ENNReal.ofReal_le_ofReal ((Complex.re_le_norm _).trans (hCb _))

  obtain ⟨hST, hfinR, hfinE, -, hcsm, -, -⟩ :=
    AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det K L
  haveI := hST; haveI := hfinR; haveI := hfinE; haveI := hcsm
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0)

  obtain ⟨Rg₀, hRg₀⟩ := hg.isBounded.subset_closedBall (0 : Fin 2 → mixedEmbedding.mixedSpace L)
  set Rg : ℝ := max Rg₀ 0 with hRg
  have hRg0 : 0 ≤ Rg := le_max_right _ _
  have hgz : ∀ y : Fin 2 → mixedEmbedding.mixedSpace L, Rg < ‖y‖ → g y = 0 := by
    intro y hy
    by_contra h
    have hmem : y ∈ tsupport g := subset_tsupport _ h
    have := hRg₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact absurd (this.trans (le_max_left _ _)) (not_le.2 hy)

  have hvanish : ∀ (m : ℕ) (f : Fin m → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ f →
      (Submodule.span ℝ (Set.range f) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) = Dinf →
      ∃ κ : ℝ, 0 < κ ∧ ∀ cc : Fin m → ℝ, κ * Rg < ‖cc‖ → G (∑ i, cc i • f i) = 0 := by
    intro m f hf hfs
    obtain ⟨κ, hκ, hinj⟩ :=
      AutomorphicForm.exists_pos_forall_norm_le_mul_norm_archIdent_sum_smul_mulVec_tmul_of_linearIndependent_of_span_eq
        K L h2 σ hgen δ₀ c u hN hns v hv m f hf hfs
    refine ⟨κ, hκ, fun cc hcc => ?_⟩
    have hmem : (∑ i, cc i • f i) ∈ Dinf := by
      rw [← hfs]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    simp only [hG, Set.indicator_of_mem hmem]
    have : g (archcol (∑ i, cc i • f i)) = 0 := by
      apply hgz
      by_contra hle
      rw [not_lt] at hle
      have h1 := hinj cc
      have h2 : κ * ‖archcol (∑ i, cc i • f i)‖ ≤ κ * Rg := mul_le_mul_of_nonneg_left hle hκ.le
      simp only [harchcol] at h2
      linarith
    rw [this]; simp

  obtain ⟨Scpt, hScpt, hGS⟩ : ∃ S : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      IsCompact S ∧ ∀ X ∉ S, G X = 0 := by
    obtain ⟨κ, hκ, hκv⟩ := hvanish n₂ e₂ hli hspan
    have hφ : Continuous fun cc : Fin n₂ → ℝ => ∑ i, cc i • e₂ i :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
    refine ⟨(fun cc : Fin n₂ → ℝ => ∑ i, cc i • e₂ i) '' Metric.closedBall 0 (κ * Rg),
      (isCompact_closedBall _ _).image hφ, fun X hX => ?_⟩
    by_cases hXD : X ∈ Dinf
    · have hXs : X ∈ Submodule.span ℝ (Set.range e₂) := by
        rw [← SetLike.mem_coe, hspan]; exact hXD
      obtain ⟨cc, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hXs
      apply hκv cc
      by_contra hle
      rw [not_lt] at hle
      exact hX ⟨cc, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
    · simp only [hG, Set.indicator_of_notMem hXD]

  have hdecay : ∀ s' : ℝ, 1 < s' →
      (∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ →
        (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) = Dinf →
        ∃ r C : ℝ, (n₂ : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s' - 1) < r ∧
          ∀ cc : Fin n₂ → ℝ, G (∑ i, cc i • e₂ i) ≤ ENNReal.ofReal (C * (1 + ‖cc‖) ^ (-r))) := by
    intro s' hs' m f hf hfs
    obtain ⟨κ, hκ, hκv⟩ := hvanish m f hf hfs
    set r : ℝ := (m : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s' - 1) + 1 with hr
    have hr0 : 0 < r := by
      have : (0 : ℝ) ≤ 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s' - 1) := by positivity [sub_pos.2 hs']
      rw [hr]; positivity
    refine ⟨r, Cb * (1 + κ * Rg) ^ r, by rw [hr]; linarith, fun cc => ?_⟩
    rcases lt_or_ge (κ * Rg) ‖cc‖ with hfar | hnear
    · rw [hκv cc hfar]; exact zero_le
    · refine (hGC _).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : 0 < 1 + ‖cc‖ := by positivity
      have h2 : (1 + κ * Rg) ^ (-r) ≤ (1 + ‖cc‖) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)
      have h3 : (1 + κ * Rg) ^ r * (1 + κ * Rg) ^ (-r) = 1 := by
        rw [Real.rpow_neg (by positivity), mul_inv_cancel₀ (Real.rpow_pos_of_pos (by positivity) _).ne']
      calc Cb = Cb * ((1 + κ * Rg) ^ r * (1 + κ * Rg) ^ (-r)) := by rw [h3, mul_one]
        _ = Cb * (1 + κ * Rg) ^ r * (1 + κ * Rg) ^ (-r) := by ring
        _ ≤ Cb * (1 + κ * Rg) ^ r * (1 + ‖cc‖) ^ (-r) := by
            apply mul_le_mul_of_nonneg_left h2
            exact mul_nonneg hCb0 (Real.rpow_nonneg (by positivity) _)

  have hs : s ≠ ⊤ :=
    AutomorphicForm.ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul K L σ _ τa' hτa' s _ hmap

  have hZ := AutomorphicForm.lintegral_twistedCentralizer_mul_indicator_mul_ideleNorm_det_rpow_eq_mul_lintegral_arch_mul_dedekindZeta_mul_prod_of_forall_le_mul_one_add_norm_rpow_neg
    K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s harch t S₀ ht hfin τ' hτ' cτ' hcτ' hτ'prod v hv μ₁ hμ₁ U G hGm S₁ hS₁ W hWm hW₀ hW₁ hunit Corr hCorr hCorr₁

  have hbridge : ∀ s' : ℝ, (∫⁻ t, ENNReal.ofReal
          (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1) *
            U.indicator (fun _ => (1 : ℂ)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2)).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s') ∂τ') = (∫⁻ t, G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          U.indicator (fun _ => (1 : ℝ≥0∞)) (fun i =>
              ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s') ∂τ') := by

    have hmemT : ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
        ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
          GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∈ Dinf := by
      intro t
      have h1 := (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _).1 t.2
      rw [AutomorphicForm.mem_twistedCommutant_iff] at h1
      have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
        M.map (AutomorphicForm.tensorArchHom K L)) h1
      beta_reduce at h2
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map] at h2
      have hσ : (AutomorphicForm.tensorArchHom K L : L ⊗[K] AdeleRing (𝓞 K) K → L ⊗[K] InfiniteAdeleRing K) ∘
          (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ) =
          (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) ∘ (AutomorphicForm.tensorArchHom K L) := by
        funext z; exact AutomorphicForm.tensorArchHom_sigmaTensor K L σ z
      rw [hσ, ← Matrix.map_map] at h2
      simp only [hDinf, Set.mem_setOf_eq]
      exact h2

    have hcol : ∀ (t : ↥(AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) (i : Fin 2),
        ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1 =
        AutomorphicForm.archIdent K L ((((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
          GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).mulVec
            fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i) := by
      intro t i
      have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
      have e2 : ∀ x y : AdeleRing (𝓞 L) L, (x + y).1 = x.1 + y.1 := fun _ _ => rfl
      have ea : ∀ j, (algebraMap L (AdeleRing (𝓞 L) L) (v j)).1 =
          AutomorphicForm.archIdent K L ((v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) := by
        intro j
        rw [← AutomorphicForm.baseChangeEquiv_tmul_one (K := K), AutomorphicForm.fst_baseChangeEquiv,
          AutomorphicForm.tensorArchHom_tmul]
        rfl
      have eb : ∀ j, (((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 =
          AutomorphicForm.archIdent K L (((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
            GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) :=
        fun j => AutomorphicForm.fst_baseChangeEquiv K L _
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1, e2, ea, eb, map_add, map_mul]
    intro s'
    congr 1
    funext t
    have hGt : G ((AutomorphicForm.tensorArch K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
          GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
          ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).1)).re := by
      simp only [hG, Set.indicator_of_mem (hmemT t), harchcol, hcol]
    rw [hGt]
    by_cases hU : (fun i => ((((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) i).2) ∈ U
    · simp only [Set.indicator_of_mem hU, mul_one]
    · simp only [Set.indicator_of_notMem hU, mul_zero, Complex.zero_re, ENNReal.ofReal_zero, zero_mul]

  have hcov : (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) * ∏ v ∈ S₁, Corr v 1 =
        (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
          ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2) := by
    have hmem : ∀ cc : Fin n₂ → ℝ, (∑ i, cc i • e₂ i) ∈ Dinf := by
      intro cc
      rw [← hspan]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hGe : ∀ cc : Fin n₂ → ℝ, G (∑ i, cc i • e₂ i) = ENNReal.ofReal (g (archcol (∑ i, cc i • e₂ i))).re := by
      intro cc
      simp only [hG]
      exact Set.indicator_of_mem (hmem cc) _
    simp_rw [hGe, harchcol]
    exact hE8 n₂ e₂ hli hspan

  have hlim := AutomorphicForm.tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
    K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s harch t S₀ ht hfin τ' hτ' cτ' hcτ' hτ'prod v hv μ₁ hμ₁ U g S₁ G hGm (ENNReal.ofReal Cb) ENNReal.ofReal_ne_top hGC Scpt hScpt hGS hs Corr
      (fun v hv => ⟨(hCorr₁ v hv).2, (hCorr₁ v hv).1⟩) n₂ e₂ hli hmap hcov

  refine (Filter.tendsto_congr' ?_).2 hlim
  filter_upwards [self_mem_nhdsWithin] with s' hs'
  have hs' : 1 < s' := hs'
  rw [hbridge s', hZ s' hs' (by simpa only [hDinf] using hdecay s' hs')]

end S_AutomorphicForm_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_mul_lintegral_twistedCentralizer_schwartzMap_mul_indicator_nhdsGT_one_of_level_of_covol (solution)
