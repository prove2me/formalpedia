-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.gaussOne_of_damped
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:10.466954+00:00
-- url     : https://prove2.me/submissions/9e969743-dd03-411d-ab33-30807faabb1d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (h : GaussOneDamped) : GaussOne := by
  intro β a hβ ha
  have h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), ((‖β‖ / Real.sqrt (4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2) : ℝ) : ℂ) =
      ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (a * w ^ 2 / 2) ∂(mu β) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ using (h β a δ hδ).symm
  refine Filter.Tendsto.congr' h1 ?_
  have hb : 0 < ‖β‖ := norm_pos_iff.2 hβ
  have hab : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hc : ContinuousAt (fun δ:ℝ => ‖β‖ / Real.sqrt (4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2)) 0 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    have : 0 < 4 * (0:ℝ) ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 := by positivity
    exact (Real.sqrt_pos.2 this).ne'
  have h2 := (Complex.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  convert h2 using 2
  simp only [Function.comp]
  congr 1
  have : 4 * (0:ℝ) ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 = (‖β‖ * ‖a‖) ^ 2 := by ring
  show ‖a‖⁻¹ = ‖β‖ / Real.sqrt (4 * (0:ℝ) ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2)
  rw [this, Real.sqrt_sq (by positivity)]
  field_simp
end Formalism.FourierDecayAlt.P.G9
