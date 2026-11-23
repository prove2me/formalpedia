-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.injOn_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:07.717559+00:00
-- url     : https://prove2.me/submissions/50920e1f-fd8a-49e7-89e3-8c5ab028188b

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
theorem _root_.solution (s k : ℕ) (u : ℂ) (hu : u ≠ 0) : InjOn (fun z => u⁻¹ * z ^ s) (A s k) := by
  intro z hz z' hz' e
  have e' : z ^ s = z' ^ s := mul_left_cancel₀ (inv_ne_zero hu) e
  rw [← hz.2, ← hz'.2, e']
end Formalism.FourierDecayAlt.P.NthRootMeasurability
