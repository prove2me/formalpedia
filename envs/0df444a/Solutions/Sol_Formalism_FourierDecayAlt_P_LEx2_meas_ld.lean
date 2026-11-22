-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.meas_ld
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:35.358914+00:00
-- url     : https://prove2.me/submissions/051cd6f8-156f-4e35-ad54-75d108bacf00

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (p : ℕ) (φ : ℝ → ℝ) (h : SmoothLog φ) : Measurable (ld p φ) := by
  unfold ld
  have : Continuous (iteratedDeriv p (fun u : ℝ => φ (Real.exp u))) :=
    h.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  exact this.measurable.comp Real.measurable_log
end Formalism.FourierDecayAlt.P.LEx2
