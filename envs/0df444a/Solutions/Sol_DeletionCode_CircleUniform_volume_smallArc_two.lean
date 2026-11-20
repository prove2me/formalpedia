-- Prove2me | solution 1 for DeletionCode.CircleUniform.volume_smallArc_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:13.133221+00:00
-- url     : https://prove2.me/submissions/4c51a1ec-0bcf-4c38-8f22-7c3f3c3f40d0

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
import Theorems.Thm_DeletionCode_CircleUniform_volume_smallArc

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution : volume (smallArc 2) = 1 := by
  simpa using volume_smallArc 2 (by decide)
end DeletionCode.CircleUniform
