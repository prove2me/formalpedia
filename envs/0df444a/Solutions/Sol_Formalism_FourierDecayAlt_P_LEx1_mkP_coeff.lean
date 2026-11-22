-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.mkP_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:00.938482+00:00
-- url     : https://prove2.me/submissions/11bd3978-df0d-4875-abc8-6e6b108c256c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
open Polynomial
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (m : ℕ) (c : ℕ → ℂ) (k : ℕ) : (mkP m c).coeff k = if k < m + 1 then c k else 0 := by
  simp [mkP, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
end Formalism.FourierDecayAlt.P.LEx1
