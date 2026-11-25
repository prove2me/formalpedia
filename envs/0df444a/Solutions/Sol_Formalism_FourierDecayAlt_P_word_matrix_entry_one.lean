-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.word_matrix_entry_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:16.865599+00:00
-- url     : https://prove2.me/submissions/2b74d181-cfca-4f60-8230-47d84e293d90

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_entry_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.EntryOne := by
  intro K A S _ _ _ _ _ _ _ _ QQ w hw
  exact Wd7.entry_one QQ w hw
end Formalism.FourierDecayAlt.P
