-- Prove2me | solution 1 for Formalism.L2.Th1.H.haar_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:22.561264+00:00
-- url     : https://prove2.me/submissions/d09d0178-0d25-4624-a1f0-f24d8401b736

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {n : Type*} [Fintype n] (Φ : (n → ℂ) ≃ₗ[ℂ] V) :
    ∃ κ : ℝ, ∀ f : V → ℂ, (Integrable (fun w => f (Φ w)) → Integrable f μ) ∧
      ∫ z, f z ∂μ = (κ : ℂ) * ∫ w, f (Φ w) := by
  classical
  let Ψ : (n → ℂ) ≃L[ℂ] V := Φ.toContinuousLinearEquiv
  let ν : Measure V := Measure.map Ψ volume
  have hme : MeasurableEmbedding Ψ := Ψ.toHomeomorph.measurableEmbedding
  obtain ⟨c, hμ⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  subst hμ
  refine ⟨(c : ℝ), fun f => ⟨fun hf => ?_, ?_⟩⟩
  · apply Integrable.smul_measure_nnreal
    rw [hme.integrable_map_iff]
    exact hf
  · rw [integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul]
    try rfl
end Formalism.L2.Th1.H
