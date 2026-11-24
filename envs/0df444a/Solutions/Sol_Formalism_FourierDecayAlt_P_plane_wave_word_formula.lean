-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plane_wave_word_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:39.623444+00:00
-- url     : https://prove2.me/submissions/49ed8feb-e7d5-4f58-8fb4-339af7fa1604

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_top_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_planeLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_word_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PlaneWaveWord := by
  intro R M _ _ _ _ _ _ Ξ n K dat grid X X' hS hg
  have h := word_gen Ξ (2 * n) X X' K dat grid (fun a => (dat a).s)
    (fun a Q Q' => top_extract (planeLetter Ξ n (dat a) (Q • X) (Q' • X') (hS a).1 (hS a).2)
      (grid a) (hg a)) 1 1
  simpa only [one_smul] using h
end Formalism.FourierDecayAlt.P
