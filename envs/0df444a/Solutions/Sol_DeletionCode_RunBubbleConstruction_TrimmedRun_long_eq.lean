-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.TrimmedRun.long_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:38:02.33575+00:00
-- url     : https://prove2.me/submissions/52e48441-d9e0-4fda-b29f-2ea74324f50e

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction

set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.TrimmedRun
variable {k rho : ℕ} {pre suffix : List Bool} {bit : Bool} {orientation : Orientation}
namespace DeletionCode.RunBubbleConstruction.TrimmedRun
theorem _root_.solution (r : TrimmedRun k pre suffix rho bit orientation) :
    pre ++ List.replicate rho bit ++ suffix =
      r.before ++ r.bubble.longWord ++ r.after := by
  calc
    _ = (r.before ++ r.bubble.left) ++ List.replicate rho bit ++
        (r.bubble.right ++ r.after) :=
      congrArg₂ (fun (p s : List Bool) => p ++ List.replicate rho bit ++ s)
        r.pre_eq r.suffix_eq
    _ = _ := by
      simp only [BubbleWord.longWord, r.rho_eq, r.bit_eq, List.append_assoc]
end DeletionCode.RunBubbleConstruction.TrimmedRun
