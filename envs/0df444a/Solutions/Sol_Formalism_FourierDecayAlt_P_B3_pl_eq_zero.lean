-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:30:15.048281+00:00
-- url     : https://prove2.me/submissions/fdeee304-e80c-4136-924f-c680020eaf95

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
theorem _root_.solution {a b k x : ℝ} (hk : 0 ≤ k) (hx : x ∉ Ioo a b) : pl a b k x = 0 := by
  unfold pl
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
  rcases hx with hx | hx
  · rw [Real.smoothTransition.zero_of_nonpos (show k * (x - a) ≤ 0 by nlinarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (show k * (b - x) ≤ 0 by nlinarith), mul_zero]
end Formalism.FourierDecayAlt.P.B3
