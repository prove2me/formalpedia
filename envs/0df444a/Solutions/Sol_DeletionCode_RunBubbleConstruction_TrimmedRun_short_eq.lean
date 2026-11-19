-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.TrimmedRun.short_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:38:07.801475+00:00
-- url     : https://prove2.me/submissions/098d1c2c-6a5c-4911-93cd-14bc3987cc5f

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction

set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}
namespace DeletionCode.RunBubbleConstruction.TrimmedRun
theorem _root_.solution (r : TrimmedRun k pre suffix rho bit orientation) :
    pre ++ List.replicate (rho - 1) bit ++ suffix =
      r.before ++ r.bubble.shortWord ++ r.after := by
  calc
    _ = (r.before ++ r.bubble.left) ++ List.replicate (rho - 1) bit ++
        (r.bubble.right ++ r.after) :=
      congrArg₂ (fun (p s : List Bool) => p ++ List.replicate (rho - 1) bit ++ s)
        r.pre_eq r.suffix_eq
    _ = _ := by
      simp only [BubbleWord.shortWord, r.rho_eq, r.bit_eq, List.append_assoc]
end DeletionCode.RunBubbleConstruction.TrimmedRun
