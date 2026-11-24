-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.v_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:41.458162+00:00
-- url     : https://prove2.me/submissions/113b08f7-44c6-495f-8411-bf3cb7b279d6

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
theorem _root_.solution {P T : Type*} [MeasurableSpace P] [MeasurableSpace T] {μ : Measure P} {ν : Measure T}
    [SFinite μ] [SFinite ν]
    (W : T → ℂ) (hW : Integrable W ν) (ξ : T → P → ℂ) (hξm : Measurable (fun a : T × P => ξ a.1 a.2))
    (hξ : ∀ τ p, ‖ξ τ p‖ = 1)
    (k : P → P → ℂ) (hk : Integrable (fun a : P × P => k a.1 a.2) (μ.prod μ)) :
    Integrable (fun τ => W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ) ν ∧
    (∫ τ, W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ ∂ν) =
      ∫ p, ∫ p', (∫ τ, W τ * ξ τ p' ∂ν) * k p p' ∂μ ∂μ := by
  have base : Integrable (fun z : T × (P × P) => W z.1 * k z.2.1 z.2.2) (ν.prod (μ.prod μ)) :=
    hW.mul_prod hk
  have hm : Measurable fun z : T × (P × P) => ξ z.1 z.2.2 :=
    hξm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hInt : Integrable (Function.uncurry fun (τ : T) (a : P × P) => ξ τ a.2 * (W τ * k a.1 a.2))
      (ν.prod (μ.prod μ)) := by
    refine base.mono (hm.aestronglyMeasurable.mul base.1) (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, norm_mul, hξ, one_mul, le_refl]
  have hτ : ∀ τ, W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ = ∫ a : P × P, ξ τ a.2 * (W τ * k a.1 a.2) ∂(μ.prod μ) := by
    intro τ
    have hi : Integrable (fun a : P × P => ξ τ a.2 * k a.1 a.2) (μ.prod μ) := by
      have hm' : Measurable fun a : P × P => ξ τ a.2 := hξm.comp (measurable_const.prodMk measurable_snd)
      refine hk.mono (hm'.aestronglyMeasurable.mul hk.1) (ae_of_all _ fun z => ?_)
      simp only [norm_mul, hξ, one_mul, le_refl]
    rw [← integral_prod (fun a : P × P => ξ τ a.2 * k a.1 a.2) hi, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    ring
  constructor
  · have := hInt.integral_prod_left
    refine this.congr (ae_of_all _ fun τ => ?_)
    exact (hτ τ).symm
  · simp_rw [hτ]
    rw [integral_integral_swap hInt]
    have hr := hInt.integral_prod_right
    have e : ∀ a : P × P, (∫ τ, ξ τ a.2 * (W τ * k a.1 a.2) ∂ν) = (∫ τ, W τ * ξ τ a.2 ∂ν) * k a.1 a.2 := by
      intro a
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      ring
    have hr' : Integrable (fun a : P × P => (∫ τ, W τ * ξ τ a.2 ∂ν) * k a.1 a.2) (μ.prod μ) :=
      hr.congr (ae_of_all _ fun a => e a)
    rw [← integral_prod (fun a : P × P => (∫ τ, W τ * ξ τ a.2 ∂ν) * k a.1 a.2) hr']
    exact integral_congr_ae (ae_of_all _ fun a => e a)
end Formalism.FourierDecayAlt.P.B7
