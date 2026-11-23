-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_mul_le_gP_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:30.85581+00:00
-- url     : https://prove2.me/submissions/c59ef7c8-9bcb-4bad-90e4-985ef1ad463a

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (π : ι → V →L[ℝ] ℂ) (c u : V) : gP π c * gP π u ≤ gP π (c + u) := by
  unfold gP
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => ?_)
  rw [← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have := norm_add_le (π v c) (π v u)
  rw [map_add]
  nlinarith [norm_nonneg (π v c), norm_nonneg (π v u), mul_nonneg (norm_nonneg (π v c)) (norm_nonneg (π v u))]
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
