-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:41.582453+00:00
-- url     : https://prove2.me/submissions/eeee04b8-a1ee-402c-aebb-0af635bf1f02

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] :
    finrank ℚ E = 2 * deg E := by
  have h2 : finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  unfold deg; omega
end Formalism.FourierDecayAlt.P.S6x5
