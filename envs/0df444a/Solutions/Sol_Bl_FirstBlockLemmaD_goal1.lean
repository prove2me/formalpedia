-- Prove2me | solution 1 for Bl.FirstBlockLemmaD.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:49.462808+00:00
-- url     : https://prove2.me/submissions/009ae9c0-9e0c-4cf1-878c-36ab3a3d2be2

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaD
namespace Bl.FirstBlockLemmaD
theorem _root_.solution :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] (x y : PadicAlgCl p),
  LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) (Max.max.{0} (Norm.norm.{0} x) (Norm.norm.{0} y)) := by
  intro p inst x y
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rw [norm_neg, ← sub_eq_add_neg] at h
  exact h
end Bl.FirstBlockLemmaD
