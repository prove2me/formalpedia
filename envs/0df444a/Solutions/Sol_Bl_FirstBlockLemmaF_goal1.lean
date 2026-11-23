-- Prove2me | solution 1 for Bl.FirstBlockLemmaF.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:17.152799+00:00
-- url     : https://prove2.me/submissions/d64d2983-59e1-4a93-891f-d3b96cc268ea

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaF_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaF
namespace Bl.FirstBlockLemmaF
theorem _root_.solution :
  ∀ (p : Nat) [hp : Fact (Nat.Prime p)] {a b : PadicComplex p} {c : Real},
  LE.le.{0} (Norm.norm.{0} a) c → LE.le.{0} (Norm.norm.{0} b) c → LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) c := by
  intro p hp a b c ha hb
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha ?_)
  rw [norm_neg]
  exact hb
end Bl.FirstBlockLemmaF
