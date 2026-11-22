-- Prove2me | solution 1 for Formalism.HadamardInequality.P.hadamard_inequality_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:59:11.08403+00:00
-- url     : https://prove2.me/submissions/2fa2f8d3-df2f-464f-b590-36c91d6b1b03

import Mathlib
import Definitions.Def_Formalism_GelfandTransference_Statement
import Definitions.Def_Lemmata_DetNormLeProdRows_DetNormLeProdRows
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Theorems.Thm_Bl_DetNormLeProdRows_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution : Formalism.HadamardInequality.Hadamard := by
  first | exact Bl.DetNormLeProdRows.goal1 .. | (apply Bl.DetNormLeProdRows.goal1 <;> assumption) | (intros; apply Bl.DetNormLeProdRows.goal1 <;> assumption)
end Formalism.HadamardInequality.P
