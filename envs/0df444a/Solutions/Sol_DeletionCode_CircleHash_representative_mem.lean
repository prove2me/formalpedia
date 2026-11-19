-- Prove2me | solution 1 for DeletionCode.CircleHash.representative_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:28:10.843773+00:00
-- url     : https://prove2.me/submissions/a71d6558-aed5-4ff0-a8a7-96985ca27d0a

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (z : UnitAddCircle) :
    representative z ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 z).property
end DeletionCode.CircleHash
