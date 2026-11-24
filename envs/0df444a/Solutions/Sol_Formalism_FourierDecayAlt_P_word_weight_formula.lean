-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.word_weight_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.876378+00:00
-- url     : https://prove2.me/submissions/0bcbc1e9-52e2-4c49-a2e4-0d13a51a1c91

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_ProductFactorBounds_letter_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.WordWeight := by
  intro K _ q x w Y h
  induction w with
  | nil => simp [qW, xW]
  | cons l w ih =>
    have hl := letter_ratio l Y (h l (by simp))
    have hw := ih (fun g hg => h g (by simp [hg]))
    simp only [qW, xW, List.map_cons, List.prod_cons]
    rw [mul_div_mul_comm, hw, hl]
    ring
end Formalism.FourierDecayAlt.P
