-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.negative_step_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:11:32.443799+00:00
-- url     : https://prove2.me/submissions/bf71e309-fdfc-49c0-85be-42fe47d7d3b3

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {H : Type*} (p q : H → ℚ)
    (hp : BooleanVector p) (hq : BooleanVector q) (h : H)
    (hneg : (q - p) h = -1) : p h = 1 := by
  have hp' := hp h
  have hq' := hq h
  change q h - p h = -1 at hneg
  rcases hp' with hp' | hp'
  · rcases hq' with hq' | hq' <;> linarith
  · exact hp'
end DeletionCode.WitnessAlgebra
