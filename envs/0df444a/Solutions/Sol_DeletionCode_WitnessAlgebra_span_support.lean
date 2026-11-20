-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.span_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:08.104182+00:00
-- url     : https://prove2.me/submissions/46143aff-63e5-42b8-8849-3059595f1f87

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
import Theorems.Thm_DeletionCode_WitnessAlgebra_span_zero_at

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {H : Type*} (S : Set (H → ℚ)) (u : H → ℚ)
    (hu : u ∈ Submodule.span ℚ S) (h : H) (hne : u h ≠ 0) :
    ∃ w ∈ S, w h ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  exact hne (span_zero_at S h hnone u hu)
end DeletionCode.WitnessAlgebra
