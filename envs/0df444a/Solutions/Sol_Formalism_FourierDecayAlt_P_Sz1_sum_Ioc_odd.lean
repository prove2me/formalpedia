-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.sum_Ioc_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:03.246264+00:00
-- url     : https://prove2.me/submissions/1839be99-7413-409b-a43f-c817606f75a6

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_two_sum_Ioc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz1
theorem _root_.solution (k r : ℕ) :
    ∑ M ∈ Ioc k (k + (2 * r + 1)), M = (2 * r + 1) * k + (r + 1) * (2 * r + 1) := by
  have h := two_sum_Ioc k (2 * r + 1)
  have h2 : 2 * ((2 * r + 1) * k) + (2 * r + 1) * (2 * r + 1 + 1) =
      2 * ((2 * r + 1) * k + (r + 1) * (2 * r + 1)) := by ring
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
end Formalism.FourierDecayAlt.P.Sz1
