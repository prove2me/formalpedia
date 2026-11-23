-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.measurable_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:37.091411+00:00
-- url     : https://prove2.me/submissions/09579461-2a56-4e91-b7cb-c716d97e8f8e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) :
    Measurable (fun x : Fin d → ℂ => W *ᵥ x) := by
  have : Continuous (fun x : Fin d → ℂ => W *ᵥ x) := by fun_prop
  exact this.measurable
end Formalism.FourierDecayAlt.P.G8
