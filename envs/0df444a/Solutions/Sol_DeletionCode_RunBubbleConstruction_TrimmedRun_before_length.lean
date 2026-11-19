-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.TrimmedRun.before_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:38:12.565237+00:00
-- url     : https://prove2.me/submissions/2793fb00-88a1-4b5f-a13e-a8c95ae936be

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction

set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}
namespace DeletionCode.RunBubbleConstruction.TrimmedRun
theorem _root_.solution (r : TrimmedRun k pre suffix rho bit orientation) :
    r.before.length + (windowLength k - rho) = pre.length := by
  have h := congrArg List.length r.pre_eq
  simpa only [List.length_append, r.bubble.left_length, r.rho_eq] using h.symm
end DeletionCode.RunBubbleConstruction.TrimmedRun
