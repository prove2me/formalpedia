-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:16.714846+00:00
-- url     : https://prove2.me/submissions/40064b9c-4e14-4f88-aea6-31812fc4313a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Theorems.Thm_Formalism_FourierDecayAlt_P_star_generators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.LevelStar := by
  intro P L hL
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩ := hL
  have hS := star_generators P
  refine ⟨?_, ?_, ?_⟩
  · rw [hz, hzb]
    exact hS.2.1
  · rw [hn, hns]
    exact hS.2.2.2.2.2
  · rw [hT]
    simp [Complex.star_def, Complex.conj_ofReal]
end Formalism.FourierDecayAlt.P
