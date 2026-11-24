-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2.AB_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:29:03.851817+00:00
-- url     : https://prove2.me/submissions/a1d9a685-f3cc-4d76-b691-524e45fc21a7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open Formalism.FourierDecayAlt.P.B2
namespace Formalism.FourierDecayAlt.P.B2
theorem _root_.solution (k r : ℕ) : (0 : ℝ) ≤ AB k r := by
  unfold AB
  positivity
end Formalism.FourierDecayAlt.P.B2
