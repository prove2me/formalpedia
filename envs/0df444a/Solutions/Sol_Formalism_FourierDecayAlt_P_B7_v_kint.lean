-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.v_kint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:40.643782+00:00
-- url     : https://prove2.me/submissions/2bee2dab-5ac4-4988-a977-dcd13309b2ca

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

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
theorem _root_.solution {P E : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ)
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p')
    (hkm : AEStronglyMeasurable (fun a : P × P => k a.1 a.2) (μ.prod μ)) :
    Integrable (fun a : P × P => k a.1 a.2) (μ.prod μ) := by
  have hmp : ∀ p, S p → Integrable (fun p' => ‖u (T p p')‖) μ := fun p hp =>
    (((hT p hp).integrable_comp_emb (hTe p hp)).2 hu).norm
  have hsec : ∀ᵐ p ∂μ, AEStronglyMeasurable (fun p' => k p p') μ := by
    first
      | exact hkm.prodMk_left
      | exact hkm.prod_mk_left
  rw [integrable_prod_iff hkm]
  constructor
  · filter_upwards [hS, hsec] with p hp hpm
    refine Integrable.mono' ((hmp p hp).const_mul ‖u p‖) hpm ?_
    filter_upwards [hS] with p' hp'
    rw [← hk p p' hp hp']
    exact norm_inner_le_norm _ _
  · refine Integrable.mono' (hu.norm.const_mul (∫ x, ‖u x‖ ∂μ)) hkm.norm.integral_prod_right' ?_
    filter_upwards [hS] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ p', ‖k p p'‖ ∂μ ≤ ∫ p', ‖u p‖ * ‖u (T p p')‖ ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) ((hmp p hp).const_mul _) ?_
          filter_upwards [hS] with p' hp'
          rw [← hk p p' hp hp']
          exact norm_inner_le_norm _ _
      _ = ‖u p‖ * ∫ x, ‖u x‖ ∂μ := by
          rw [integral_const_mul]
          congr 1
          exact (hT p hp).integral_comp (hTe p hp) (fun x => ‖u x‖)
      _ = (∫ x, ‖u x‖ ∂μ) * ‖u p‖ := mul_comm _ _
end Formalism.FourierDecayAlt.P.B7
