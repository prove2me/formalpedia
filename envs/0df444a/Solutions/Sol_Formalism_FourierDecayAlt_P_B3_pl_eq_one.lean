-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:38:35.319382+00:00
-- url     : https://prove2.me/submissions/5cf51497-1126-4668-a998-013c19a48f10

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {a b k x : ℝ} (h1 : 1 ≤ k * (x - a)) (h2 : 1 ≤ k * (b - x)) : pl a b k x = 1 := by
  unfold pl
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]
end Formalism.FourierDecayAlt.P.B3
