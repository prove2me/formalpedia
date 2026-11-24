-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_insertion_diagonal_compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:32.571802+00:00
-- url     : https://prove2.me/submissions/542e2fb0-0377-43d0-8bf9-dedb5aad0207

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.InsDiag := by
  intro K A S _ _ _ _ _ _ _ _ a b
  exact ⟨Wd1.ins_one a, Wd1.insert_diagonal_extract a b⟩
end Formalism.FourierDecayAlt.P
