-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:01:58.582274+00:00
-- url     : https://prove2.me/submissions/711e238c-c630-4e48-95f9-f8c08fe0daba

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_eq_one

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
theorem _root_.solution {a b x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo a b) : pl (a / 2) (b + 1) (2 / a + 1) x = 1 := by
  have hpos : 0 < 2 / a := div_pos two_pos ha
  have h2a : 2 / a * (a / 2) = 1 := by field_simp
  apply pl_eq_one
  · nlinarith [mul_nonneg hpos.le (by linarith [hx.1] : (0:ℝ) ≤ x - a / 2 - a / 2), hx.1]
  · nlinarith [mul_nonneg hpos.le (by linarith [hx.2] : (0:ℝ) ≤ b + 1 - x), hx.2]
end Formalism.FourierDecayAlt.P.B3
