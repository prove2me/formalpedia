-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz9.vand_word_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:58.666799+00:00
-- url     : https://prove2.me/submissions/9ccc6715-574d-4f75-adb5-31a3e7fea997

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_vand_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_anti_of_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz9
theorem _root_.solution (hIL : Interlacing) (c : Cfg) (de : ℕ → ℝ) (hOk : c.Ok)
    (hde : IsWord c.k de) : 0 < Vand c.k (c.u de) := by
  unfold Interlacing at hIL
  obtain ⟨h1, -⟩ := hIL c de hOk hde
  refine vand_pos _ _ (anti_of_step _ _ (fun i hi1 hi2 => ?_))
  have hx := h1 i hi1 hi2
  linarith [hx.1, hx.2]
end Formalism.FourierDecayAlt.P.Sz9
