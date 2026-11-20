-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.span_zero_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:47.639333+00:00
-- url     : https://prove2.me/submissions/a31c1fee-d7f5-41ad-a388-0a82c0b0ea9a

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {H : Type*} (S : Set (H → ℚ)) (h : H)
    (hzero : ∀ w ∈ S, w h = 0) (u : H → ℚ) (hu : u ∈ Submodule.span ℚ S) :
    u h = 0 := by
  induction hu using Submodule.span_induction with
  | mem w hw => exact hzero w hw
  | zero => rfl
  | add x y hx hy hix hiy => simp [hix, hiy]
  | smul a x hx hix => simp [hix]
end DeletionCode.WitnessAlgebra
