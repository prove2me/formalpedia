-- Prove2me | solution 1 for Formalism.H.gauss_fun_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:28.161435+00:00
-- url     : https://prove2.me/submissions/271e328b-a4d2-4c20-814c-73951f9e5d59

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
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =
      fun v : V => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
  funext v
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring
end Formalism.H
