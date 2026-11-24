-- Prove2me | solution 1 for Formalism.H.gauss_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:08.479895+00:00
-- url     : https://prove2.me/submissions/567e6908-bfb4-43d4-871b-eacf407c89cb

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (t : ℝ) :
    Continuous (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
end Formalism.H
