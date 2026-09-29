-- Prove2me | solution 1 for AutomorphicForm.tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2e313d88-826b-5bc9-958c-252c70230c79

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
import Theorems.Thm_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem ResidueCore.core
    (K : Type) [Field K] [NumberField K]
    (Z A : ℝ → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ⊤)
    (hA : Filter.Tendsto A (nhdsWithin 1 (Set.Ioi 1)) (nhds a))
    (hZ : ∀ s : ℝ, 1 < s →
      Z s = A s * ENNReal.ofReal ((NumberField.dedekindZeta K (2 * (s : ℂ)) *
        NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re)) :
    Filter.Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * Z s) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (a * ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K / 2))) := by
  obtain ⟨-, hE7⟩ := NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT K

  have hre : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta K (2 * (s : ℂ)) *
        NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) (𝓝[>] 1)
      (𝓝 ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K / 2)) := by
    have h := (Complex.continuous_re.tendsto _).comp hE7
    have h1 : ∀ s : ℝ, (((s : ℂ) - 1) * (NumberField.dedekindZeta K (2 * (s : ℂ)) *
        NumberField.dedekindZeta K (2 * (s : ℂ) - 1))).re =
        (s - 1) * (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re := by
      intro s
      rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have h2 : (NumberField.dedekindZeta K 2 * ((NumberField.dedekindZeta_residue K / 2 : ℝ) : ℂ)).re =
        (NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K / 2 := by
      rw [mul_comm, Complex.re_ofReal_mul]; ring
    simp only [Function.comp_def, h1, h2] at h
    exact h
  have hB : Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * ENNReal.ofReal ((NumberField.dedekindZeta K (2 * (s : ℂ)) *
        NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re)) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K / 2))) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hre
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) ≤ s - 1 := by
      have : (1 : ℝ) < s := hs
      linarith
    simp only [Function.comp_apply]
    rw [← ENNReal.ofReal_mul hs']
  have hAB := ENNReal.Tendsto.mul hA (Or.inr ENNReal.ofReal_ne_top) hB (Or.inr ha)
  refine hAB.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hZ s hs]
  ring

set_option maxHeartbeats 4000000 in
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

    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G) (C : ℝ≥0∞) (hC : C ≠ ⊤) (hGC : ∀ X, G X ≤ C)
    (S : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) (hS : IsCompact S) (hGS : ∀ X ∉ S, G X = 0)
    (hs : s ≠ ⊤)
    (Corr : HeightOneSpectrum (𝓞 K) → ℝ → ℝ≥0∞)
    (hCorr : ∀ v ∈ S₁, Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)) ∧ Corr v 1 ≠ ⊤) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) →

      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) * ∏ v ∈ S₁, Corr v 1 =
        (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
          ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2) →
      Tendsto (fun s' : ℝ => ENNReal.ofReal (s' - 1) *
          (ENNReal.ofReal cτ' * (∫⁻ t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))), G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
              ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s') ∂τa') *
            (ENNReal.ofReal ((NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ)) *
                NumberField.dedekindZeta K (2 * ((s' : ℝ) : ℂ) - 1)).re) * ∏ v ∈ S₁, Corr v s')))
        (𝓝[>] (1 : ℝ))
        (𝓝 (2⁻¹ * ((∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
          (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
            ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
              NumberField.dedekindZeta_residue K))))) := by
  letI iRK : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI iRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  letI mM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  intro n₂ e₂ he hτ hE8

  obtain ⟨hfin, htend, hval⟩ :=
    AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram
      K L σ (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τa' s hs G hGm C hC hGC S hS hGS n₂ e₂ he hτ
  have hXfin : s * (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) ≠ ⊤ := by
    rw [← hval]; exact (hfin 1 le_rfl).ne

  have hP : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), (∀ v ∈ T, Tendsto (Corr v) (𝓝[>] (1 : ℝ)) (𝓝 (Corr v 1)) ∧ Corr v 1 ≠ ⊤) →
      Tendsto (fun s' : ℝ => ∏ v ∈ T, Corr v s') (𝓝[>] (1 : ℝ)) (𝓝 (∏ v ∈ T, Corr v 1)) ∧ (∏ v ∈ T, Corr v 1) ≠ ⊤ := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert v T hv ih =>
      intro h
      obtain ⟨ih1, ih2⟩ := ih (fun w hw => h w (Finset.mem_insert_of_mem hw))
      obtain ⟨hv1, hv2⟩ := h v (Finset.mem_insert_self v T)
      refine ⟨?_, ?_⟩
      · simp only [Finset.prod_insert hv]
        exact ENNReal.Tendsto.mul hv1 (Or.inr ih2) ih1 (Or.inr hv2)
      · rw [Finset.prod_insert hv]; exact ENNReal.mul_ne_top hv2 ih2
  obtain ⟨hP1, hP2⟩ := hP S₁ hCorr

  have ha : ENNReal.ofReal cτ' * (s * (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i))) * ∏ v ∈ S₁, Corr v 1 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXfin) hP2
  have h1c := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal cτ') htend (Or.inr ENNReal.ofReal_ne_top)
  have hA := ENNReal.Tendsto.mul h1c (Or.inr hP2) hP1
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXfin))

  have hres := ResidueCore.core K _ _ _ ha hA (fun s' _ => rfl)

  have h1 : ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
      NumberField.dedekindZeta_residue K) =
      ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2) *
        ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K) := by
    rw [mul_assoc, ENNReal.ofReal_mul (sq_nonneg _)]
  have h2 : ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K / 2) =
      ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K) * 2⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, div_eq_mul_inv]
  have hvalue : ENNReal.ofReal cτ' * (s * (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i))) * (∏ v ∈ S₁, Corr v 1) *
        ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K / 2) =
      2⁻¹ * ((∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) *
          (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
            ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
              NumberField.dedekindZeta_residue K))) := by
    rw [h1, h2]
    calc ENNReal.ofReal cτ' * (s * (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i))) * (∏ v ∈ S₁, Corr v 1) *
          (ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K) * 2⁻¹)
        = ENNReal.ofReal cτ' * s * ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K) * 2⁻¹ *
          ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) * ∏ v ∈ S₁, Corr v 1) := by ring
      _ = ENNReal.ofReal cτ' * s * ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K) * 2⁻¹ *
          ((∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
              U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
          ENNReal.ofReal ((NumberField.discr K : ℝ) ^ 2)) := by rw [hE8]
      _ = _ := by ring
  rw [← hvalue]
  refine hres.congr' (Filter.Eventually.of_forall fun s' => ?_)
  ring

end S_AutomorphicForm_tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume
end P2MW
export P2MW.S_AutomorphicForm_tendsto_sub_one_mul_archFactor_mul_dedekindZeta_mul_prod_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram_of_covolume (solution)
