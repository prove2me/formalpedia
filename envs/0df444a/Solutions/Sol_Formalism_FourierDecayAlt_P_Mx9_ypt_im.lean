-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx9.ypt_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:15.649578+00:00
-- url     : https://prove2.me/submissions/501e425d-4544-460a-b04e-38376f24c660

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9
namespace Formalism.FourierDecayAlt.P.Mx9
theorem _root_.solution {S : Type} (a : Letter ℂ S) (h : a.pt.im = 0) : (ypt a).im = 0 := by
  unfold ypt
  split_ifs <;> simp [h]
end Formalism.FourierDecayAlt.P.Mx9
