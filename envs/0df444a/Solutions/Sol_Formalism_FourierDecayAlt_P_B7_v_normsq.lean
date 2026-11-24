-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.v_normsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:04.822204+00:00
-- url     : https://prove2.me/submissions/18f24b16-1f04-44be-b182-e417cdcc27ec

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_int_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ) (ξ : P → ℂ) (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1)
    (hξT : ∀ p p', S p → S p' → ξ (T p p') = ξ p * ξ p')
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p') :
    (((‖∫ p, ξ p • u p ∂μ‖ ^ 2 : ℝ)) : ℂ) = ∫ p, ∫ p', ξ p' * k p p' ∂μ ∂μ := by
  have hi : Integrable (fun p => ξ p • u p) μ := v_int_smul hu hξm hξ
  have h1 : (((‖∫ p, ξ p • u p ∂μ‖ ^ 2 : ℝ)) : ℂ) = inner ℂ (∫ p, ξ p • u p ∂μ) (∫ p, ξ p • u p ∂μ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    try rfl
  rw [h1, ← inner_conj_symm, ← integral_inner hi, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hS] with p hp
  rw [inner_conj_symm, inner_smul_left, v_inner S hS T hT hTe u hu ξ hξm hξ hξT k hk p hp, ← mul_assoc,
    RCLike.conj_mul, hξ p]
  simp
end Formalism.FourierDecayAlt.P.B7
