-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx4.rd_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:20.407805+00:00
-- url     : https://prove2.me/submissions/cca8f1ca-d006-44fb-a95b-6ed76a4df419

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Jx4
namespace Formalism.FourierDecayAlt.P.Jx4
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  have h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  unfold S6.rd
  first
    | exact Real.rpow_pos_of_pos h _
    | exact Real.rpow_pos h _
end Formalism.FourierDecayAlt.P.Jx4
