-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:44.284391+00:00
-- url     : https://prove2.me/submissions/7590e619-d256-429b-8859-f59ee57218d5

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
omit [MeasurableSpace V] [BorelSpace V]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (Λ : Submodule ℤ V) (φ : V → ℂ) (hc : Continuous φ) (h : LocSummable Λ φ) :
    Continuous (fun x : V => ∑' l : Λ, φ ((l:V) + x)) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨b, hb, hbd⟩ := h (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  have hon : ContinuousOn (fun x : V => ∑' l : Λ, φ ((l : V) + x)) (Metric.closedBall x₀ 1) :=
    continuousOn_tsum (fun l => (hc.comp (continuous_const.add continuous_id)).continuousOn) hb
      (fun l x hx => hbd l x hx)
  exact hon.continuousAt (Metric.closedBall_mem_nhds x₀ one_pos)
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
