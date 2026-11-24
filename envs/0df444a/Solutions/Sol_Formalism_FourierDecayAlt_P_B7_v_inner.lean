-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.v_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:45.629097+00:00
-- url     : https://prove2.me/submissions/79df7eef-90da-4d3f-a118-e9f822e3708c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_int_smul

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
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p')
    (p : P) (hp : S p) :
    inner ℂ (u p) (∫ p', ξ p' • u p' ∂μ) = ξ p * ∫ p', ξ p' * k p p' ∂μ := by
  have hTp := hT p hp
  have e1 : (∫ p', ξ p' • u p' ∂μ) = ∫ p', ξ (T p p') • u (T p p') ∂μ :=
    (hTp.integral_comp (hTe p hp) (fun p' => ξ p' • u p')).symm
  have e2 : (fun p' => ξ (T p p') • u (T p p')) =ᵐ[μ] fun p' => (ξ p * ξ p') • u (T p p') := by
    filter_upwards [hS] with p' hp'
    rw [hξT p p' hp hp']
  have hint : Integrable (fun p' => (ξ p * ξ p') • u (T p p')) μ :=
    v_int_smul ((hTp.integrable_comp_emb (hTe p hp)).2 hu) (measurable_const.mul hξm)
      (fun p' => by rw [norm_mul, hξ, hξ, one_mul])
  rw [e1, integral_congr_ae e2, ← integral_inner hint (u p), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hS] with p' hp'
  rw [inner_smul_right, hk p p' hp hp', mul_assoc]
end Formalism.FourierDecayAlt.P.B7
