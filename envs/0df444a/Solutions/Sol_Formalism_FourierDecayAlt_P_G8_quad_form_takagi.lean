-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.quad_form_takagi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:51.559651+00:00
-- url     : https://prove2.me/submissions/1087502a-af8a-4285-b978-7e31a08b9eda

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
theorem _root_.solution (d : ℕ) (W D : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    x ⬝ᵥ ((W * D * Wᵀ) *ᵥ x) = (Wᵀ *ᵥ x) ⬝ᵥ (D *ᵥ (Wᵀ *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
end Formalism.FourierDecayAlt.P.G8
